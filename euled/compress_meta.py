"""Euled meta-compressor: an optimizer that optimizes the compression optimizer.

Metric: ProofOptimizer's own proof-length function (po_length.py, arXiv 2510.15700 Appendix L), summed per declaration.
Their P5 numbers: 8658 -> 4002 (53.8%).

Operators (each proposes a smaller file; every proposal is compiled whole by AXLE before it is kept):
  dce        delete one top-level tactic step (dead steps the rest never needed)
  shortcut   proof-state graph skip edge: replace steps k..end of a declaration with one short tactic
  closer     replace one `have` block's proof with the shortest single tactic that works
  shared     graphify across declarations: a `have` statement proved in 2+ places becomes one shared lemma
  inline     a lemma used once is folded into its caller as a `have`, saving the restated binders
  bridge     model proposes one bridging lemma that collapses several lemmas, then unused lemmas are deleted
  fresh      model writes a fresh short proof of one declaration from its statement alone
Meta layer: a bandit (UCB) picks the next operator by PO tokens saved per Lean check so far.
Stops when one full round across all operators saves under 1%, or the budget ends.
Every round is logged with its quantified gain; a safety gate checks theorem statements are unchanged every round.
"""
import asyncio, json, math, os, re, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import po_length as P
import compress_long as C
import euled_evo as E
import euled_evo2 as V
from euled_evo import lean_block, log

HERE = os.path.dirname(os.path.abspath(__file__))
PROB = C.PROB
LIVE = os.path.expanduser(f"~/euled-site/euled-app/dist/live/compress_{PROB}.activity.json")
ORIG = {"P1": 36478, "P3": 16377, "P4": 29147, "P5": 8658}  # ProofOptimizer paper, original lengths (their count)
POPT = {"P1": 20506, "P3": 7907, "P4": 14531, "P5": 4002}  # ProofOptimizer paper, simplified lengths
SHORT = ["grind", "linarith", "nlinarith", "positivity", "omega", "norm_num", "simp_all", "aesop", "field_simp", "ring_nf",
         "simp", "tauto", "nlinarith [sq_nonneg _, mul_pos ‹_› ‹_›]", "norm_num at * <;> linarith", "simp_all <;> nlinarith"]
MAX_CHECKS = int(os.environ.get("EULED_META_CHECKS", "2500"))


def po(text):
    """Strict ProofOptimizer length: their tokenizer, theorem statements free, lemma statements COUNTED
    (otherwise moving work into new lemma statements would look free). Original P5 = 10671."""
    _, ds, _ = C.blocks(text)
    return sum(P.proof_length(d) if C.locked(d) else len(P.lexer(P.remove_comments(d)).split()) for d in ds if d)


def loose(text):
    """ProofOptimizer's exact count: every declaration's statement free (reproduces their paper's originals)."""
    _, ds, _ = C.blocks(text)
    return sum(P.proof_length(d) for d in ds if d)


def steps(decl):
    """Split a declaration into (head ':= by', [top-level step strings]) using indentation."""
    m = re.search(r":=\s*by\s*\n", decl)
    if not m:
        return None, None
    head, body = decl[:m.end()], decl[m.end():]
    lines = body.split("\n")
    ind = min((len(l) - len(l.lstrip()) for l in lines if l.strip()), default=2)
    out = []
    for l in lines:
        if l.strip() and len(l) - len(l.lstrip()) == ind and not l.lstrip().startswith(("|", "<;>")):
            out.append(l)
        elif out:
            out[-1] += "\n" + l
        else:
            out.append(l)
    return head, [s for s in out if s.strip()], ind


def join(head, st):
    return head + "\n".join(st)


class Meta:
    def __init__(self, text):
        self.ctx = C.Ctx()
        self.text = text
        self.lock = C.theorems(text)
        self.orig_strict = int(os.environ.get("EULED_ORIG_STRICT", "0")) or po(text)
        self.orig_loose = int(os.environ.get("EULED_ORIG_LOOSE", "0")) or loose(text)
        self.stats = {k: {"saved": 0, "checks": 0, "tries": 0} for k in ("dce", "shortcut", "closer", "shared", "inline", "bridge", "fresh")}
        self.stats["stretch"] = {"saved": 0, "checks": 0, "tries": 0}
        self.rounds = []
        self.t0 = time.time()

    async def ok(self, t):
        return await self.ctx.ok(t)

    def parts(self):
        return C.blocks(self.text)

    async def accept(self, cand, op):
        before = po(self.text)
        if po(cand) < before and C.theorems(cand) == self.lock and await self.ok(cand):
            self.text = cand
            self.stats[op]["saved"] += before - po(cand)
            log(f"{op}: {before} -> {po(cand)} PO tokens")
            self.publish(op)
            return True
        return False

    def publish(self, op=""):
        try:
            os.makedirs(os.path.dirname(LIVE), exist_ok=True)
            act = {"updated": time.strftime("%Y-%m-%d %H:%M:%S"), "problem": f"IMO 2025 {PROB} (Seed-Prover proof)",
                   "metric": "ProofOptimizer proof length", "original": self.orig_strict, "proofoptimizer_pct": round(100 * (1 - POPT[PROB] / ORIG[PROB]), 1), "loose_now": loose(self.text), "loose_orig": self.orig_loose,
                   "now": po(self.text), "last_operator": op, "checks": self.ctx.calls, "rounds": self.rounds,
                   "operators": self.stats}
            json.dump(act, open(LIVE + ".tmp", "w")); os.replace(LIVE + ".tmp", LIVE)
        except Exception:
            pass

    # ---------- operators: each runs one sweep and returns PO tokens saved ----------
    async def op_dce(self):
        h, ds, t = self.parts(); saved0 = po(self.text)
        for i in sorted(range(len(ds)), key=lambda i: -P.proof_length(ds[i])):
            h, ds, t = self.parts()
            if i >= len(ds) or not ds[i]:
                continue
            head, st, _ = steps(ds[i]) if steps(ds[i])[0] else (None, None, None)
            if not st or len(st) < 2:
                continue
            cands, news = [], []
            for k in range(len(st) - 1):
                nd = list(ds); nd[i] = join(head, st[:k] + st[k + 1:]); cands.append(C.assemble(h, nd, t)); news.append(nd[i])
            res = await asyncio.gather(*[C.ok_local(self.ctx, h, ds, t, i, nd_i) for nd_i in news])
            good = [c for c, r in zip(cands, res) if r]
            # greedy: apply the best, then try combining the rest one at a time
            for c in sorted(good, key=po):
                if await self.accept(c, "dce"):
                    break
        return saved0 - po(self.text)

    async def op_shortcut(self):
        saved0 = po(self.text)
        h, ds, t = self.parts()
        for i in sorted(range(len(ds)), key=lambda i: -P.proof_length(ds[i])):
            h, ds, t = self.parts()
            if i >= len(ds) or not ds[i] or not steps(ds[i])[0]:
                continue
            head, st, ind = steps(ds[i])
            pad = " " * ind
            cands = []
            for k in range(len(st)):
                for tac in SHORT[:5]:
                    nd = list(ds); nd[i] = join(head, st[:k] + [pad + tac]); c = C.assemble(h, nd, t)
                    if po(c) < po(self.text):
                        cands.append((c, nd[i]))
            cands.sort(key=lambda x: po(x[0]))
            for chunk in range(0, min(len(cands), 48), 24):
                part = cands[chunk:chunk + 24]
                res = await asyncio.gather(*[C.ok_local(self.ctx, h, ds, t, i, d_) for _, d_ in part])
                hit = [c for (c, _), r in zip(part, res) if r]
                if hit and await self.accept(min(hit, key=po), "shortcut"):
                    break
        return saved0 - po(self.text)

    async def op_closer(self):
        saved0 = po(self.text)
        h, ds, t = self.parts()
        for i in range(len(ds)):
            h, ds, t = self.parts()
            if i >= len(ds) or not ds[i]:
                continue
            for m in list(re.finditer(r"(have\s+[^\n]*?:=\s*by)((?:\n[ \t]+[^\n]*)+)", ds[i])):
                blk = m.group(2)
                if P.proof_length("x := by" + blk) < 6:
                    continue
                hind = len(ds[i][:m.start()].split("\n")[-1]) + 2
                cands, news = [], []
                for tac in SHORT:
                    nd = list(ds); nd[i] = ds[i][:m.start()] + m.group(1) + " " + tac + ds[i][m.end():]
                    cands.append(C.assemble(h, nd, t)); news.append(nd[i])
                res = await asyncio.gather(*[C.ok_local(self.ctx, h, ds, t, i, d_) for d_ in news])
                hit = [c for c, r in zip(cands, res) if r]
                if hit and await self.accept(min(hit, key=po), "closer"):
                    break  # declaration text changed; rescan next sweep
        return saved0 - po(self.text)

    async def op_shared(self):
        saved0 = po(self.text)
        h, ds, t = self.parts()
        seen = {}
        for i, d in enumerate(ds):
            for m in re.finditer(r"have\s+(\w+)\s*:\s*([^\n]+?)\s*:=\s*by((?:\n[ \t]+[^\n]*)+|[^\n]*)", d):
                key = re.sub(r"\s+", " ", m.group(2))
                seen.setdefault(key, []).append((i, m))
        for key, occ in sorted(seen.items(), key=lambda kv: -len(kv[1]) * len(kv[0])):
            if len({i for i, _ in occ}) < 2:
                continue
            # binders: hypotheses named in the statement must exist in every caller; lemma takes the caller's binders
            i0, m0 = occ[0]
            stmt0 = C.split_decl(ds[i0])[0]
            binders = re.sub(r"^(lemma|theorem)\s+\S+", "", stmt0).rsplit(":", 1)[0]
            name = f"euled_shared{abs(hash(key)) % 10**6}"
            lem = f"lemma {name} {binders} : {key} := by" + m0.group(3)
            nd = list(ds)
            for i, m in occ:
                nd[i] = nd[i].replace(m.group(0), f"have {m.group(1)} : {key} := by\n    first | exact {name} (by assumption) | (apply {name} <;> assumption)", 1)
            cand = C.assemble(h, [lem] + nd, t)
            if await self.accept(cand, "shared"):
                h, ds, t = self.parts()
        return saved0 - po(self.text)

    async def op_inline(self):
        saved0 = po(self.text)
        h, ds, t = self.parts()
        for i, d in enumerate(ds):
            if not d or C.locked(d):
                continue
            name = re.match(r"lemma\s+(\S+)", d).group(1)
            users = [j for j, e in enumerate(ds) if j != i and e and re.search(r"\b" + re.escape(name) + r"\b", e)]
            if len(users) != 1:
                continue
            j = users[0]
            stmt, body = C.split_decl(d)
            prop = stmt.rsplit(":", 1)[-1].strip() if ")" in stmt else stmt
            # ask the model to fold it; cheap and robust to binder renaming
            out = await asyncio.to_thread(C.haiku,
                "Lean 4 + Mathlib (Lean 4.21). Fold the helper lemma into the main declaration as a `have` (or delete it if the main proof does not need it), "
                "making the total as short as possible. Keep the main declaration's statement exactly. Return only the main declaration in one ```lean block.\n"
                f"```lean\n{d}\n\n{ds[j]}\n```")
            if not out:
                continue
            m = re.search(r"(lemma|theorem)\s", out)
            if not m:
                continue
            _, nb = C.split_decl(out[m.start():])
            if not nb.strip():
                continue
            nd = list(ds); nd[j] = C.split_decl(ds[j])[0] + " := by" + nb; nd[i] = ""
            if await self.accept(C.assemble(h, nd, t), "inline"):
                h, ds, t = self.parts()
        return saved0 - po(self.text)

    async def op_bridge(self):
        """Graphify step: show the model the lemma graph (statements, sizes, who uses whom) and ask for ONE bridging lemma
        that lets the main theorems skip the most lemmas. Then delete whatever nobody uses."""
        saved0 = po(self.text)
        h, ds, t = self.parts()
        names = [re.match(r"(?:lemma|theorem)\s+(\S+)", d).group(1) if d else "" for d in ds]
        graph = []
        for i, d in enumerate(ds):
            if not d:
                continue
            uses = [names[j] for j in range(len(ds)) if j != i and names[j] and re.search(r"\b" + re.escape(names[j]) + r"\b", d)]
            graph.append(f"- {names[i]} ({P.proof_length(d)} tokens) uses {uses or 'nothing'}:\n  {C.split_decl(d)[0][:600]}")
        for _ in range(2):
            out = await asyncio.to_thread(C.haiku,
                "Lean 4 + Mathlib (Lean 4.21). Below is the dependency graph of a proof file: each declaration, its size, what it uses, and its statement.\n"
                + "\n".join(graph) +
                "\n\nFind the shortest route: propose ONE new bridging lemma (any true statement, with a short proof) that connects the hypotheses to the "
                "theorems more directly, so several lemmas become unnecessary. Then reprove every `theorem` using it. Keep every theorem statement EXACTLY. "
                "Return a complete replacement file body (lemmas then theorems, no imports, no namespace) in one ```lean block.")
            if not out:
                continue
            out = out.replace("import Mathlib", "")
            _, nds, _ = C.blocks("x\n" + out.strip() + "\n")
            if not nds:
                continue
            # keep original statements for theorems, model bodies
            orig_thm = {re.match(r"theorem\s+(\S+)", d).group(1): d for d in ds if C.locked(d)}
            fixed = []
            for d in nds:
                mm = re.match(r"theorem\s+(\S+)", d)
                if mm and mm.group(1) in orig_thm:
                    d = C.split_decl(orig_thm[mm.group(1)])[0] + " := by" + C.split_decl(d)[1]
                fixed.append(d)
            if C.theorems(C.assemble(h, fixed, t)) != self.lock:
                continue
            if await self.accept(C.assemble(h, fixed, t), "bridge"):
                break
            # partial: keep model lemmas + original lemmas, model theorem bodies
            mix = [d for d in fixed if not C.locked(d)] + [d for d in ds if d and not C.locked(d)] + [d for d in fixed if C.locked(d)]
            if await self.accept(C.assemble(h, mix, t), "bridge"):
                break
        await self.prune()
        return saved0 - po(self.text)

    async def op_fresh(self):
        saved0 = po(self.text)
        h, ds, t = self.parts()
        order = sorted(range(len(ds)), key=lambda i: -P.proof_length(ds[i]) if ds[i] else 0)[:5]
        res = await asyncio.gather(*[C.improve_decl(self.ctx, h, ds, t, i) for i in order])
        for i, w in zip(order, res):
            h, ds2, t = self.parts()
            if i < len(ds2) and w and P.proof_length(w) < P.proof_length(ds2[i]):
                nd = list(ds2); nd[i] = w
                await self.accept(C.assemble(h, nd, t), "fresh")
        return saved0 - po(self.text)

    async def errors(self, src):
        """Lean error messages for a candidate file (for the repair loop)."""
        try:
            async with self.ctx.sem:
                self.ctx.calls += 1
                r = await self.ctx.c.check(content=src, environment=C.ENV, timeout_seconds=400)
            return "\n".join(str(e)[:400] for e in r.lean_messages.errors[:6])
        except Exception as e:
            return type(e).__name__

    async def op_stretch(self, factor=0.9, repairs=4):
        """Reed's stretch rule: once progress plateaus, DEMAND a total 10% below the current best and do not stop
        until Lean accepts it. The cut is spread over the biggest declarations (each asked for ~40% less), each with a
        compiler-feedback repair loop (first try on Haiku, repairs on fcc, which is free). Partial wins are kept."""
        cur = po(self.text); target = int(cur * factor); saved0 = cur
        h, ds, t = self.parts()
        order = sorted([i for i in range(len(ds)) if ds[i]], key=lambda i: -P.proof_length(ds[i]))[:8]
        log(f"STRETCH: demanding {target} (now {cur}, -{cur - target})")

        async def one(i):
            h, ds, t = self.parts()
            d = ds[i]; n = P.proof_length(d); lim = max(3, int(n * 0.6))
            stmt = C.split_decl(d)[0]
            names = [re.match(r"(?:lemma|theorem)\s+(\S+)", x).group(1) for x in ds[:i] if x and re.match(r"(?:lemma|theorem)\s+(\S+)", x)]
            ask = (f"Lean 4 + Mathlib ({C.ENV}). This proof is {n} tokens. You MUST find a proof of AT MOST {lim} tokens with the same statement. "
                   f"Do not come back until it is that short and correct. Think about a different route: a stronger Mathlib lemma, one decisive "
                   f"`nlinarith`/`omega`/`positivity`/`grind` call with the right hints, or reusing these earlier lemmas: {', '.join(names[-12:]) or 'none'}. "
                   f"Return only the full declaration in one ```lean block.\n```lean\n{d}\n```")
            best = None
            out = await asyncio.to_thread(C.haiku, ask)
            for k in range(repairs + 1):
                if out:
                    m = re.search(r"(lemma|theorem)\s", out)
                    if m:
                        _, nb = C.split_decl(out[m.start():])
                        cand_d = stmt + " := by" + nb
                        if nb.strip() and P.proof_length(cand_d) < n:
                            h, ds2, t = self.parts()
                            if i < len(ds2) and ds2[i]:
                                nd = list(ds2); nd[i] = cand_d; cand = C.assemble(h, nd, t)
                                if await C.ok_local(self.ctx, h, ds2, t, i, cand_d):
                                    best = cand_d
                                    if await self.accept(cand, "stretch"):
                                        return
                                elif k < repairs:
                                    err = await self.errors(C.local_src(h, ds2, t, i, cand_d))
                                    try:
                                        txt, _ = await asyncio.to_thread(E.ask_fcc, ask + f"\n\nYour attempt:\n```lean\n{cand_d}\n```\nLean errors:\n{err}\nFix it, still at most {lim} tokens.", 0.4, 4000)
                                    except Exception:
                                        txt, _ = await asyncio.to_thread(V.ask, ask + f"\n\nLean errors on your attempt:\n{err}", 0.4, 4000, True)
                                    out = lean_block(txt)
                                    continue
                if k < repairs:
                    out = await asyncio.to_thread(C.haiku, ask)
        await asyncio.gather(*[one(i) for i in order])
        got = saved0 - po(self.text)
        log(f"STRETCH result: demanded -{saved0 - target}, got -{got} ({100 * got / max(1, saved0 - target):.0f}% of the demand)")
        self.stats.setdefault("stretch", {"saved": 0, "checks": 0, "tries": 0})["tries"] += 1
        return got

    async def prune(self):
        h, ds, t = self.parts()
        for i in range(len(ds)):
            h, ds, t = self.parts()
            if i >= len(ds) or not ds[i] or C.locked(ds[i]):
                continue
            name = re.match(r"lemma\s+(\S+)", ds[i]).group(1)
            if not any(re.search(r"\b" + re.escape(name) + r"\b", d) for j, d in enumerate(ds) if j != i):
                nd = list(ds); nd[i] = ""
                await self.accept(C.assemble(h, nd, t), "dce")

    async def run(self):
        ops = [k for k in self.stats if k != "stretch"]
        rnd = 0
        while self.ctx.calls < MAX_CHECKS:
            rnd += 1
            start, c0 = po(self.text), self.ctx.calls
            # UCB order: gain per check, with exploration bonus for untried operators
            tot = sum(s["tries"] for s in self.stats.values()) + 1
            def ucb(k):
                s = self.stats[k]
                if s["tries"] == 0:
                    return 1e9
                return s["saved"] / max(1, s["checks"]) + math.sqrt(2 * math.log(tot) / s["tries"])
            for op in sorted([o for o in ops if not (o == "shortcut" and rnd > 1)], key=ucb, reverse=True):
                if self.ctx.calls >= MAX_CHECKS:
                    break
                cb = self.ctx.calls
                try:
                    g = await getattr(self, "op_" + op)()
                except Exception as e:
                    log(op, "error", type(e).__name__, str(e)[:120]); g = 0
                s = self.stats[op]; s["tries"] += 1; s["checks"] += self.ctx.calls - cb
                log(f"round {rnd} {op}: saved {g}, total {po(self.text)}")
            # safety + bug gate every round: whole file recompiles, statements locked, no sorry/native_decide
            assert C.theorems(self.text) == self.lock, "statement lock broken"
            assert "sorry" not in self.text and "native_decide" not in self.text
            assert await self.ok(self.text), "file no longer compiles"
            end = po(self.text)
            self.rounds.append({"round": rnd, "start": start, "end": end, "pct_round": round(100 * (start - end) / start, 2),
                                "pct_total": round(100 * (1 - end / self.orig_strict), 2), "loose": loose(self.text), "checks": self.ctx.calls - c0,
                                "minutes": round((time.time() - self.t0) / 60, 1)})
            log("ROUND", self.rounds[-1])
            self.publish("round end")
            open(os.path.join(HERE, "runs", f"{PROB}_meta.lean"), "w").write(self.text)
            if (start - end) / start < 0.01:
                # plateau: apply the stretch demand; keep going only if it unlocked real progress
                self.stretches = getattr(self, "stretches", 0) + 1
                if self.stretches > int(os.environ.get("EULED_STRETCHES", "3")) or self.ctx.calls >= MAX_CHECKS:
                    break
                s0 = po(self.text)
                g = await self.op_stretch()
                self.rounds.append({"round": f"stretch {self.stretches}", "start": s0, "end": po(self.text),
                                    "pct_round": round(100 * g / s0, 2), "pct_total": round(100 * (1 - po(self.text) / self.orig_strict), 2),
                                    "demand_met_pct": round(100 * g / max(1, s0 - int(s0 * 0.9)), 1), "loose": loose(self.text)})
                self.publish("stretch")
                open(os.path.join(HERE, "runs", f"{PROB}_meta.lean"), "w").write(self.text)
                if g / s0 < 0.01:
                    break
        return self.text


async def main():
    src = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "runs", f"{PROB}_short.lean")
    text = open(src).read()
    m = Meta(text)
    assert await m.ok(text), "input does not compile"
    log("meta start", PROB, "strict", po(text), "loose", loose(text))
    m.publish("start")
    try:
        final = await m.run()
    except Exception as ex:
        log("meta crashed, keeping best verified text:", type(ex).__name__, str(ex)[:200])
        final = m.text
    rep = {"problem": PROB, "orig_strict": m.orig_strict, "orig_loose": m.orig_loose, "paper_orig": ORIG[PROB], "paper_simplified": POPT[PROB],
           "proofoptimizer_pct": round(100 * (1 - POPT[PROB] / ORIG[PROB]), 1), "input_strict": po(text), "final_strict": po(final), "final_loose": loose(final),
           "final_pct_strict": round(100 * (1 - po(final) / m.orig_strict), 2), "final_pct_loose": round(100 * (1 - loose(final) / m.orig_loose), 2), "rounds": m.rounds, "operators": m.stats, "checks": m.ctx.calls,
           "verified": await m.ok(final), "theorems_locked": C.theorems(final) == m.lock, "max_spent_total": V.max_spent()}
    open(os.path.join(HERE, "runs", f"{PROB}_meta.lean"), "w").write(final)
    json.dump(rep, open(os.path.join(HERE, "runs", f"{PROB}_meta_report.json"), "w"), indent=1)
    log("META REPORT", rep)

if __name__ == "__main__":
    asyncio.run(main())
