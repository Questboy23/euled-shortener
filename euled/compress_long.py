"""Euled compressor on a long competition proof: Seed-Prover's IMO 2025 P5 (ByteDance-Seed/Seed-Prover), the proof set
ProofOptimizer (Meta/MIT) reports about 49% average shortening on.
Fairness: the baseline is the original proof with comments stripped (comments are not proof). Port to AXLE's
lean-4.21.0 needs one edit (ambiguous `div_pos` -> `_root_.div_pos`); the original is Lean 4.14.
Per lemma, candidates (every one checked by compiling the WHOLE file with that lemma replaced):
  closers   the lemma body replaced by one automatic tactic combo
  fresh     Haiku writes the shortest proof from the statement alone (does not see the old proof), 2 tries
  ladder    Haiku rewrites the old proof to at most 50% / 30% of its length, 2 tries
Then: combine all winners (re-verified), AXLE simplify_theorems, delete lemmas nothing uses, and a second full pass
(Reed's rule: if pass 2 still shortens, pass 1 was not optimal). Output: runs/P5_short.lean and runs/P5_report.json.
Metrics: characters and cl100k tokens of non-comment, non-blank lines.
"""
import asyncio, json, os, re, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import euled_evo as E
import euled_evo2 as V
from euled_evo import CLOSERS, lean_block, log

ENV = os.environ.get("EULED_ENV", "lean-4.21.0")
PROB = os.environ.get("EULED_PROB", "P5")
SRC = os.environ.get("EULED_SRC") or f"/tmp/seedprover/SeedProver/imo2025/IMO2025/{PROB}.lean"
OUT = os.environ.get("EULED_OUT") or os.path.join(os.path.dirname(os.path.abspath(__file__)), "runs")
try:
    import tiktoken
    ENC = tiktoken.get_encoding("cl100k_base")
except Exception:
    ENC = None


PORT_FIXES = [("exact div_pos", "exact _root_.div_pos"), ("pow_le_pow_right ", "pow_le_pow_right₀ "),
              ("Nat.odd_iff_not_even", "Nat.not_even_iff_odd.symm")]


def port(t):
    """Lean 4.14 -> 4.21 Mathlib renames (one per Seed-Prover file); each was the file's only compile error."""
    for a, b in PORT_FIXES:
        t = t.replace(a, b)
    return t


def strip_comments(t):
    t = re.sub(r"/-.*?-/", "", t, flags=re.S)
    lines = [re.sub(r"\s+--.*$", "", l) if not l.strip().startswith("--") else "" for l in t.splitlines()]
    return "\n".join(l.rstrip() for l in lines if l.strip())


def size(t):
    body = strip_comments(t)
    return {"chars": sum(len(l.strip()) for l in body.splitlines()), "tokens": len(ENC.encode(body)) if ENC else None,
            "lines": len(body.splitlines())}


def blocks(t):
    """Split into header + top-level declarations (lemma/theorem at column 0)."""
    lines = t.split("\n")
    starts = [i for i, l in enumerate(lines) if re.match(r"(lemma|theorem)\s", l)]
    header = "\n".join(lines[:starts[0]])
    decls = []
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else len(lines)
        body = "\n".join(lines[s:e]).rstrip()
        tail = ""
        if k + 1 == len(starts):
            m = re.search(r"\n(end\s+IMO2025\.P\d.*)$", body, re.S)
            if m:
                tail, body = m.group(1), body[:m.start()]
        decls.append(body)
    return header, decls, tail


def locked(d):
    """Only the competition theorems are fixed targets; helper theorems are treated like lemmas."""
    if os.environ.get("EULED_LOCK") == "theorem":  # uploaded proofs: every `theorem` is a fixed target, lemmas are free
        return bool(re.match(r"theorem\s", d or ""))
    return bool(re.match(r"theorem\s+imo\d{4}_", d or ""))


def theorems(t):
    _, ds, _ = blocks(strip_comments(t) + "\n")
    return {re.sub(r"\s+", " ", split_decl(d)[0]) for d in ds if locked(d)}


def assemble(header, decls, tail):
    return header + "\n" + "\n\n".join(d for d in decls if d) + ("\n" + tail if tail else "") + "\n"


def split_decl(d):
    m = re.search(r":=\s*by\b", d)
    return (d[:m.start()].rstrip(), d[m.end():]) if m else (d, "")


class Ctx:
    def __init__(self):
        from axle import AxleClient
        self.c = AxleClient(); self.sem = asyncio.Semaphore(int(os.environ.get("EULED_SEM", "12"))); self.calls = 0
        import hashlib; self._h = lambda s: hashlib.sha1(s.encode()).hexdigest()
        self.cache_path = os.path.join(OUT, f"axle_cache_{PROB}.jsonl"); self.cache = {}
        if os.path.exists(self.cache_path):
            for l in open(self.cache_path):
                try:
                    k, v = json.loads(l); self.cache[k] = v
                except Exception:
                    pass

    async def ok(self, src, allow_sorry=False):
        key = self._h(src) + ("L" if allow_sorry else "")
        if key in self.cache:
            return self.cache[key]
        async with self.sem:
            self.calls += 1
            try:
                r = await self.c.check(content=src, environment=ENV, timeout_seconds=400)
                good = bool(r.okay) and (allow_sorry or "sorry" not in src) and "native_decide" not in src
            except Exception:
                good = False
        self.cache[key] = good
        with open(self.cache_path, "a") as fh:
            fh.write(json.dumps([key, good]) + "\n")
        return good


def stub(d):
    """Earlier declarations keep their statements; their proofs become `sorry` (a later lemma only uses statements)."""
    if not d:
        return d
    stmt, _ = split_decl(d)
    return stmt + " := by\n  sorry"


def local_src(header, decls, tail, i, cand):
    """File that checks ONLY declaration i: earlier ones stubbed, later ones dropped. 10-50x faster on big files.
    The whole real file is still compiled before anything is kept."""
    return assemble(header, [stub(d) for d in decls[:i] if d] + [cand], tail)


async def ok_local(ctx, header, decls, tail, i, cand):
    if re.search(r"\b(sorry|admit|native_decide)\b", cand):
        return False
    return await ctx.ok(local_src(header, decls, tail, i, cand), allow_sorry=True)


def haiku(prompt):
    text, _ = V.ask(prompt, 0.7, 4000, use_max=True)
    return lean_block(text)


async def improve_decl(ctx, header, decls, tail, i):
    stmt, body = split_decl(decls[i])
    best, best_n = decls[i], size(decls[i])["chars"]
    names = [re.match(r"(?:lemma|theorem)\s+(\S+)", d).group(1) for d in decls[:i] if re.match(r"(?:lemma|theorem)\s+(\S+)", d)]
    cands = [stmt + " := by\n  " + CLOSERS]
    prompt_fresh = (f"Lean 4 + Mathlib (Lean 4.21). Give the SHORTEST proof of this lemma. You may use these earlier lemmas: {', '.join(names) or 'none'}. "
                    f"Do not explain. Return only the full lemma in one ```lean block.\n```lean\n{stmt} := by\n  sorry\n```")
    for cut in (0.5, 0.3):
        lim = max(1, int(size(decls[i])["lines"] * cut))
        cands.append(("LADDER", f"Lean 4 + Mathlib (Lean 4.21). Rewrite this proof to at most {lim} lines, same statement, no sorry. "
                                f"Strong tactics (nlinarith, positivity, omega, simp, aesop, tauto, linarith) are fine. Return only the full lemma in one ```lean block.\n```lean\n{strip_comments(decls[i])}\n```"))
    cands += [("FRESH", prompt_fresh), ("FRESH", prompt_fresh)]
    for c in cands:
        if isinstance(c, tuple):
            out = await asyncio.to_thread(haiku, c[1])
            if not out:
                continue
            out = out.replace("import Mathlib", "").strip()
            m = re.search(r"(lemma|theorem)\s", out)
            if not m:
                continue
            _, nb = split_decl(out[m.start():])
            if not nb.strip():
                continue
            c = stmt + " := by" + nb
        if size(c)["chars"] >= best_n:
            continue
        if await ok_local(ctx, header, decls, tail, i, c):
            best, best_n = c, size(c)["chars"]
            log(f"decl {i}: {size(decls[i])['chars']} -> {best_n} chars")
    return best


async def one_pass(ctx, text):
    header, decls, tail = blocks(text)
    order = sorted(range(len(decls)), key=lambda i: -size(decls[i])["chars"])
    new = list(decls)
    winners = await asyncio.gather(*[improve_decl(ctx, header, decls, tail, i) for i in order])
    for i, w in zip(order, winners):
        new[i] = w
    combined = assemble(header, new, tail)
    if not await ctx.ok(combined):  # winners interfere: apply one at a time, biggest saving first
        cur = list(decls)
        for i in sorted(order, key=lambda i: size(decls[i])["chars"] - size(new[i])["chars"], reverse=True):
            trial = list(cur); trial[i] = new[i]
            if await ctx.ok(assemble(header, trial, tail)):
                cur = trial
        combined = assemble(header, cur, tail)
    # lemma surgery: delete declarations nothing references
    header, decls, tail = blocks(combined)
    for i in range(len(decls) - 1):
        if not decls[i] or locked(decls[i]):
            continue
        name = re.match(r"(?:lemma|theorem)\s+(\S+)", decls[i]).group(1)
        if not any(re.search(r"\b" + re.escape(name) + r"\b", d) for j, d in enumerate(decls) if j != i):
            trial = list(decls); trial[i] = ""
            if await ctx.ok(assemble(header, trial, tail)):
                decls = trial; log("deleted unused", name)
    return assemble(header, decls, tail)


async def main():
    ctx = Ctx(); t0 = time.time()
    orig = open(SRC).read()
    ported = port(orig)
    if not await ctx.ok(ported):
        ported = re.sub(r"(?<![\w.])div_pos\b", "_root_.div_pos", orig)
    assert await ctx.ok(ported), "port failed"
    base = "\n".join(l for l in strip_comments(ported).splitlines() if not l.startswith("#print")) + "\n"
    if os.environ.get("EULED_IN"):
        base = open(os.environ["EULED_IN"]).read()
    assert await ctx.ok(base), "comment stripping broke the file"
    log("baseline", size(base))
    p1 = await one_pass(ctx, base)
    try:
        s = await ctx.c.simplify_theorems(content=p1, environment=ENV, timeout_seconds=400)
        if size(s.content)["chars"] < size(p1)["chars"] and await ctx.ok(s.content):
            p1 = s.content
    except Exception:
        pass
    log("pass 1", size(p1))
    hist = [size(base)["chars"], size(p1)["chars"]]
    cur = p1
    for k in range(2, 6):
        nxt = await one_pass(ctx, cur)
        log(f"pass {k}", size(nxt))
        if size(nxt)["chars"] >= size(cur)["chars"]:
            break
        cur = nxt; hist.append(size(cur)["chars"])
    p2 = cur
    final = cur
    assert theorems(final) == theorems(base), "INTEGRITY FAIL: a theorem was dropped or its statement changed"
    ok = await ctx.ok(final)
    rep = {"original_with_comments": size(orig), "baseline_no_comments": size(base), "pass1": size(p1), "pass2": size(p2),
           "final": size(final), "verified_final": ok, "pct_shorter_chars": round(100 * (1 - size(final)["chars"] / size(base)["chars"]), 1),
           "pct_shorter_tokens": round(100 * (1 - size(final)["tokens"] / size(base)["tokens"]), 1) if ENC else None,
           "pass_history_chars": hist, "theorems_locked": sorted(theorems(final)), "checks": ctx.calls,
           "minutes": round((time.time() - t0) / 60, 1), "max_spent_total": V.max_spent(), "reference": "ProofOptimizer: about 49% average on Seed-Prover IMO 2025 proofs"}
    open(os.path.join(OUT, f"{PROB}_short.lean"), "w").write(final)
    json.dump(rep, open(os.path.join(OUT, f"{PROB}_report.json"), "w"), indent=1)
    log("REPORT", rep)

if __name__ == "__main__":
    asyncio.run(main())
