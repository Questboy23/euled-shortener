"""Euled Evo v2: every approach is a switch, so tune.py can search over them (self-optimization).

Adds to v1 (euled_evo.py primitives are reused):
  papers      : TheoremSearch API (api.theoremsearch.com, 11.7M arXiv + ProofWiki statements, free) gives the nearest
                published theorems to the goal (up to 100) and to top nodes (10 each); their slogans are fed to the
                proposer as literature hints and stored as paper nodes with links.
  ontology    : each node gets tags (from the proposer), an arXiv category (from its nearest paper) and the Mathlib
                identifiers it uses; pairs that share ontology get a bonus when ordering pairing attempts.
  generalize  : backward proposals may be universal statements ("for all m ...") that specialize to the goal;
                every generation the top backward nodes are also attacked directly from the context (one model proof
                + closers), which is how induction enters.
  mutate      : clonal mutation, the best backward nodes get explicit small-edit children.
  sketch      : informal-first arm, the model writes a natural-language proof, then a Lean skeleton with
                `have h_i : ... := by sorry` steps; each step is filled by closers, then by the model.
  direct      : whole-proof model attempts (baseline arm).
Compressor v2 (all verified by AXLE against the original statement): simplify fixpoint, one-closer whole proof,
  re-prove from scratch with only the statement (N fresh tries, shortest wins), ladder 80/70/60/50%, second pass.
Max budget guard: Claude Haiku calls only while logs/max_spent_evo.txt < EULED_MAX_BUDGET (default $15).
"""
import asyncio, json, os, random, re, time
import euled_evo as E
from euled_evo import Checker, Node, closeness, lean_block, parse_json_list, CLOSERS, wsteps, log

SPENT = os.path.expanduser("~/euled-site/logs/max_spent_evo.txt")
BUDGET = float(os.environ.get("EULED_MAX_BUDGET", "15"))


def max_spent():
    try:
        return float(open(SPENT).read().strip())
    except Exception:
        return 0.0


def ask(prompt, temp=0.8, max_tokens=2500, use_max=False):
    if use_max and max_spent() < BUDGET:
        before = E.STATS.get("max_cost_usd", 0)
        try:
            text, tok = E.ask_max(prompt)
            spent = E.STATS.get("max_cost_usd", 0) - before
            open(SPENT, "w").write(f"{max_spent() + spent:.4f}")
            if text.strip():
                E.STATS["max"] = E.STATS.get("max", 0) + 1
                return text, tok
        except Exception as e:
            log("max error", type(e).__name__)
    E.USE_MAX = False
    return E.ask(prompt, temp, max_tokens)


def papers(query, n):
    import requests
    try:
        r = requests.post("https://api.theoremsearch.com/search", json={"query": query, "n_results": n}, timeout=60)
        out = []
        for t in r.json().get("theorems", []):
            p = t.get("paper") or {}
            out.append({"slogan": t.get("slogan"), "body": (t.get("body") or "")[:300], "sim": round(t.get("similarity", 0), 3),
                        "source": p.get("source"), "title": p.get("title"), "link": p.get("link"), "category": p.get("primary_category")})
        return out
    except Exception:
        return []


def mathlib_ids(stmt):
    return sorted(set(re.findall(r"\b[A-Z][A-Za-z]+(?:\.[A-Za-z_]+)+\b|\bFinset\b|\bNat\b|\bReal\b|\b∑\b", stmt)))


PROPOSE = """You are helping connect two sides of a Lean 4 + Mathlib proof.
Context (Lean binders): {ctx}
Goal: {goal}
Proved facts (forward side):
{fwd}
Statements known to imply the goal (backward side):
{bwd}
Related published theorems (literature hints):
{lit}
Task: propose {k} NEW {kind}. {extra}
Each must be one Lean 4 Prop over the context variables (universal statements over a fresh variable are allowed),
valid Mathlib syntax, no `sorry`. Give each 1-3 ontology tags (subject or technique).
Do not explain. Respond with ONLY a JSON list, first character [ :
[{{"stmt": "...", "tags": ["..."], "proof": "tactic proof (lines after := by) or empty", "reference": "for backward statements only: the named published criterion or theorem showing it implies the goal, or empty"}}]"""


class Run:
    def __init__(self, prob, cfg):
        self.p, self.cfg = prob, cfg
        self.chk = Checker(); self.tokens = 0; self.t0 = time.time(); self.lit = []; self.papers = []

    def say(self, prompt, temp=0.8, max_tokens=3000):
        text, tok = ask(prompt, temp, max_tokens, use_max=self.cfg.get("max_proposer", False))
        self.tokens += tok
        return text

    async def say_a(self, *a, **k):
        return await asyncio.to_thread(self.say, *a, **k)

    def child(self, b, why):
        """A pending criterion became reachable: queue 'criterion implies goal' as its own problem (a conditional result)."""
        n = len([f for f in os.listdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), "problems")) if f.startswith(self.p["name"] + "__reduce")])
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "problems", f"{self.p['name']}__reduce{n}.json")
        json.dump({"name": f"{self.p['name']}__reduce{n}", "ctx": self.ctx(), "names": self.p.get("names", []),
                   "goal": f"({b.stmt}) → {self.goal()}", "informal": f"Reduction step ({getattr(b, 'ref', '')}). {why}",
                   "abstract": self.p.get("abstract", {})}, open(path, "w"), ensure_ascii=False, indent=1)
        log("CONDITIONAL:", why, "| queued", os.path.basename(path))

    def ctx(self): return self.p["ctx"]
    def goal(self): return self.p["goal"]

    async def check_thm(self, stmt_lhs, tac):
        return await self.chk.ok(f"theorem euled_t {stmt_lhs} := by\n  {tac}")

    async def prove_closed(self, stmt):
        """Prove stmt from the context alone: closers, then one model proof (this is where induction can enter)."""
        if await self.check_thm(f"{self.ctx()} : {stmt}", CLOSERS):
            return CLOSERS
        text = await self.say_a(f"Lean 4 + Mathlib. Prove:\ntheorem t {self.ctx()} : {stmt} := by\nUse induction if useful. "
                                "Return only the tactic proof (lines after `:= by`) in one ```lean block.", 0.5, 2500)
        tac = lean_block(text)
        if tac:
            tac = re.sub(r"^\s*by\b", "", tac).strip().replace("\n", "\n  ")
            if await self.check_thm(f"{self.ctx()} : {stmt}", tac):
                return tac
        return None

    # ---------------- approaches ----------------
    async def direct(self, attempts):
        for i in range(attempts):
            text = await self.say_a(f"Lean 4 + Mathlib. Prove:\ntheorem {self.p['name']} {self.ctx()} : {self.goal()} := by\n"
                                    "Return only the tactic proof (lines after `:= by`) in one ```lean block.", 0.8, 3000)
            tac = lean_block(text)
            if tac:
                tac = re.sub(r"^\s*by\b", "", tac).strip().replace("\n", "\n  ")
                src = f"theorem {self.p['name']} {self.ctx()} : {self.goal()} := by\n  {tac}"
                if await self.chk.ok(src):
                    return src
        return None

    async def sketch(self, attempts):
        """Informal-first: natural-language proof -> Lean skeleton of `have` steps with sorry -> fill each step."""
        for _ in range(attempts):
            text = await self.say_a(
                f"Lean 4 + Mathlib. Theorem:\ntheorem {self.p['name']} {self.ctx()} : {self.goal()}\n"
                f"Related literature: {'; '.join(x['slogan'] for x in self.lit[:5] if x.get('slogan'))}\n"
                "First think of a short informal proof. Then write a Lean proof skeleton: a sequence of 2-6 lines "
                "`have hK : <statement> := by sorry` followed by a final line that closes the goal using them. "
                "Return only the full theorem in one ```lean block.", 0.7, 3000)
            sk = lean_block(text)
            if not sk or "theorem" not in sk:
                continue
            sk = sk.replace("import Mathlib", "").strip()
            filled = re.sub(r":=\s*by\s+sorry", ":= by " + CLOSERS, sk)
            if "sorry" not in filled and await self.chk.ok(filled):
                return filled
            # model fills remaining steps in one call
            text = await self.say_a("Lean 4 + Mathlib. Replace every failing step so this compiles; keep the structure; no sorry. "
                                    "Return only the full theorem in one ```lean block.\n```lean\n" + filled + "\n```", 0.5, 3000)
            fixed = lean_block(text)
            if fixed and "sorry" not in fixed:
                fixed = fixed.replace("import Mathlib", "").strip()
                if f"theorem {self.p['name']}" in fixed and await self.chk.ok(fixed):
                    return fixed
        return None

    async def bracket(self):
        cfg, ctx, goal = self.cfg, self.ctx(), self.goal()
        F, B = [], []
        import ontology as O
        gid = O.add_node(goal, ctx, "goal", problem=self.p["name"])
        # consult the saved ontology: verified nodes over the same context are re-checked and reused as seeds
        for sd in O.seeds(ctx):
            if sd["kind"] == "forward" and await self.chk.ok(E.fwd_thm(ctx, sd["stmt"], sd["proof"])):
                F.append(Node("F", sd["stmt"], sd["proof"], sd["tags"], "ontology", 0))
            elif sd["kind"] == "backward" and "pending" in sd["tags"]:
                nd = Node("B", sd["stmt"], "", sd["tags"], "ontology", 0); nd.pending, nd.ref = True, ""; B.append(nd)
            elif sd["kind"] == "backward" and await self.chk.ok(E.bwd_thm(ctx, sd["stmt"], goal, sd["proof"])):
                B.append(Node("B", sd["stmt"], sd["proof"], sd["tags"], "ontology", 0))
        rel = O.related(goal, 6)
        lit = "\n".join(f"- {x['slogan']} ({x.get('source')})" for x in self.lit[:cfg.get("lit_k", 8)] if x.get("slogan")) or "- (none)"
        if rel:
            lit += "\nVerified facts from earlier Euled problems (ontology):\n" + "\n".join(f"- {r['stmt']}" for r in rel)
        if F or B:
            log(f"ontology seeds reused: F={len(F)} B={len(B)}")
        saved = set()

        def persist():
            for n in F + B:
                key = (n.side, n.stmt)
                if key in saved:
                    continue
                saved.add(key)
                i = O.add_node(n.stmt, ctx, "forward" if n.side == "F" else "backward", n.proof, n.tags, self.p["name"])
                if n.side == "B":
                    O.add_edge(i, O.nid(n.via.stmt, ctx) if n.via else gid, "implies", n.proof, self.p["name"])
            for x in self.lit[:10]:
                if x.get("slogan"):
                    pi = O.add_node(x["slogan"], "paper", "paper", x.get("link") or "", [x.get("category") or "paper"], self.p["name"])
                    O.add_edge(pi, gid, "seeds", "", self.p["name"])
            if cfg.get("live_json"):
                O.export_json(cfg["live_json"])
                act = {"updated": time.strftime("%Y-%m-%d %H:%M:%S"), "generation": g_now[0], "F": len(F), "B": len(B),
                       "tokens": self.tokens, "checks": self.chk.calls,
                       "best_forward": [n.stmt for n in F[:5]], "best_backward": [("[pending: " + getattr(n, "ref", "")[:40] + "] " if getattr(n, "pending", False) else "[verified] ") + n.stmt for n in B[:5]],
                       "log": [l for l in E.LOG[-25:]]}
                tmp = cfg["live_json"].replace(".json", ".activity.json")
                json.dump(act, open(tmp + ".tmp", "w"), ensure_ascii=False); os.replace(tmp + ".tmp", tmp)
        g_now = [0]
        for g in range(1, cfg["gens"] + 1):
            g_now[0] = g
            if time.time() - self.t0 > cfg["max_seconds"]:
                break
            nb = max(1, round(cfg["k"] * cfg["back_share"] * 2)); nf = max(1, cfg["k"] * 2 - nb)
            jobs = [self.propose("B", F, B, B[:3], nb, g, lit), self.propose("F", F, B, F[:2], nf, g, lit)]
            if cfg.get("mutate") and B:
                jobs.append(self.propose("M", F, B, B[:1], 2, g, lit))
            for nodes in await asyncio.gather(*jobs):
                for nd in nodes:
                    side = B if nd.side == "B" else F
                    if all(nd.stmt != m.stmt for m in side):
                        side.append(nd)
            # generalize / induction route: attack the top backward nodes directly from the context
            for b in B[:cfg.get("direct_back", 2)]:
                if getattr(b, "tried_closed", False):
                    continue
                b.tried_closed = True
                tac = await self.prove_closed(b.stmt)
                if tac and getattr(b, "pending", False):
                    self.child(b, "PROVED pending criterion from context; reduction to goal still open")
                    continue
                if tac:
                    f = Node("F", b.stmt, tac, ["closed"], None, g)
                    src = E.assemble(self.p, f, b, "exact hq")
                    if await self.chk.ok(src):
                        log("CLOSED backward node from context, gen", g, "|", b.stmt[:80])
                        persist()
                        O.add_edge(O.nid(b.stmt, ctx), gid, "solved", tac, self.p["name"])
                        if cfg.get("live_json"):
                            O.export_json(cfg["live_json"])
                        return src, g
            self.score(F, B)
            for side in (F, B):
                side.sort(key=lambda n: -n.fit)
                elite = {}
                for n in side:
                    elite.setdefault(n.tags[0].lower(), n)
                keep = (list(elite.values()) if cfg.get("map_elites", True) else []) + [n for n in side if n not in elite.values()]
                side[:] = sorted(keep[:cfg["cap"]], key=lambda n: -n.fit)
            log(f"gen {g}: F={len(F)} B={len(B)} tokens={self.tokens} checks={self.chk.calls}")
            persist()
            Bv = [x for x in B if not getattr(x, "pending", False)]
            Bp = [x for x in B if getattr(x, "pending", False)]
            if F and Bp:
                import connect as C
                f, b, ctac, strat = await C.connect(self, F, Bp, min(3, len(F), len(Bp)), cfg["model_pairs"])
                if f:
                    self.child(b, "CONNECTED forward fact to pending criterion: " + f.stmt[:80])
                    Bp.remove(b); B.remove(b)
            if F and Bv:
                import connect as C
                f, b, ctac, strat = await C.connect(self, F, Bv, min(5, len(F), len(Bv)), cfg["model_pairs"] * 2)
                if f:
                    src = E.assemble(self.p, f, b, ctac)
                    if await self.chk.ok(src):
                        log("CONNECTED gen", g, "| Q:", f.stmt[:60], "| P:", b.stmt[:60])
                        persist()
                        O.add_edge(O.nid(f.stmt, ctx), O.nid(b.stmt, ctx), "implies", ctac, self.p["name"])
                        O.add_edge(O.nid(b.stmt, ctx), gid, "solved", "", self.p["name"])
                        if cfg.get("live_json"):
                            O.export_json(cfg["live_json"])
                        return src, g
        return None, None

    def score(self, F, B):
        w = self.cfg.get("onto_bonus", 0.0)
        def onto(n): return set(t.lower() for t in n.tags) | set(mathlib_ids(n.stmt))
        for n in F:
            n.fit = max([closeness(n, b) + w * len(onto(n) & onto(b)) / 5 for b in B] or [0]) + 0.2 * n.a / (n.a + n.b)
        for n in B:
            n.fit = max([closeness(f, n) + w * len(onto(f) & onto(n)) / 5 for f in F] or [0]) + 0.2 * n.a / (n.a + n.b)

    async def propose(self, side, F, B, parents, k, gen, lit):
        ctx, goal = self.ctx(), self.goal()
        fwd = "\n".join(f"- {n.stmt}" for n in F[:8]) or "- (none yet)"
        bwd = "\n".join(f"- {n.stmt}" for n in B[:8]) or f"- {goal}"
        if side in ("B", "M"):
            kind = ("SMALL EDITS (mutations) of the first backward statement that are easier but still sufficient" if side == "M" else
                    "SUFFICIENT CONDITIONS: statements P such that P with the context implies the goal or a backward statement")
            extra = ("Prefer easier statements closer to the forward facts; ask what would need to be the case. "
                     + ("A universal generalization ('∀ m : ℕ, ...') that specializes to the goal is allowed and often provable by induction. " if self.cfg.get("generalize") else "")
                     + "Parents: " + ("; ".join(p.stmt for p in parents) or "the goal"))
        else:
            kind = "TRUE CONSEQUENCES of the context, each with a short tactic proof"
            extra = "Prefer facts that move toward the backward statements. Parents: " + ("; ".join(p.stmt for p in parents) or "the context")
        prompt = PROPOSE.format(ctx=ctx, goal=goal, fwd=fwd, bwd=bwd, lit=lit if self.cfg.get("papers") else "- (not used)", k=k, kind=kind, extra=extra)
        text = await self.say_a(prompt, 0.8, 4000)
        cands = parse_json_list(text)[:k]
        if not cands:
            text = await self.say_a(prompt + "\n\nREPLY WITH THE JSON LIST ONLY. FIRST CHARACTER MUST BE [", 0.5, 4000)
            cands = parse_json_list(text)[:k]

        LOGIC = {"True", "False", "Prop", "p", "q", "u", "Unit", "n", "m", "Type", "fun"}
        goal_ids = set(re.findall(r"[A-Za-z_][A-Za-z_0-9'.]*", goal))

        async def verify(c):
            s = str(c["stmt"]).strip()
            ids = set(re.findall(r"[A-Za-z_][A-Za-z_0-9'.]*", s)) - LOGIC
            if not ids:
                return None  # pure logic (True, p -> p): no mathematical content
            if side != "F" and ids <= goal_ids | LOGIC and await self.chk.ok(f"theorem euled_eq {ctx} (h : {goal}) : {s} := by\n  first | tauto | simp_all | aesop"):
                return None  # restatement of the goal with logical padding (RH ∧ True, ¬¬RH, ∀ n, RH)
            if side == "F" and self.p.get("abstract"):
                s_abs, binds = s, []
                for k_, (const, typ) in enumerate(self.p["abstract"].items()):
                    if const in s_abs:
                        s_abs = re.sub(r"\b" + re.escape(const) + r"\b", f"euled_f{k_}", s_abs); binds.append(f"(euled_f{k_} : {typ})")
                if binds and await self.chk.ok(f"theorem euled_abs {ctx} {' '.join(binds)} : {s_abs} := by\n  first | grind | (intros; by_contra; simp_all) | {CLOSERS}"):
                    return None  # true for ANY function in place of the real object: pure logic, no content
            raw = re.sub(r"^\s*by\b", "", str(c.get("proof") or "")).strip()
            tacs = [t for t in [raw.replace("\n", "\n  "), CLOSERS] if t.strip()]
            for t in tacs:
                if side == "F":
                    if await self.chk.ok(E.fwd_thm(ctx, s, t)):
                        return Node("F", s, t, c.get("tags"), parents[0].stmt if parents else None, gen)
                else:
                    if await self.chk.ok(E.bwd_thm(ctx, s, goal, t)):
                        if await self.chk.ok(f"theorem euled_eq {ctx} (h : {goal}) : {s} := by\n  {CLOSERS}") and not s.lstrip().startswith("∀"):
                            return None  # restatement of the goal
                        return Node("B", s, t, c.get("tags"), "goal", gen)
                    for b in [x for x in B if not getattr(x, "pending", False)][:4]:
                        if await self.chk.ok(E.con_thm(ctx, s, b.stmt, t)):
                            return Node("B", s, t, c.get("tags"), b.stmt, gen, via=b)
            ref = str(c.get("reference") or "").strip()
            if side == "B" and self.cfg.get("pending_backward") and len(ref) > 6 and s.lstrip().startswith(("∀", "∃", "(")):
                if await self.chk.ok(f"theorem euled_eq {ctx} (h : {goal}) : {s} := by\n  {CLOSERS}"):
                    return None  # trivially implied by the goal: a restatement, not a criterion
                if not await self.chk.ok(f"example {ctx} : ({s}) ∨ ¬({s}) := by\n  exact Classical.em _"):
                    return None  # does not even typecheck
                nd = Node("B", s, "", list(c.get("tags") or ["criterion"]) + ["pending"], "goal", gen)
                nd.pending, nd.ref = True, ref
                return nd
            return None
        return [r for r in await asyncio.gather(*[verify(c) for c in cands]) if r]

    async def solve(self):
        cfg = self.cfg
        direct_src = f"theorem {self.p['name']} {self.ctx()} : {self.goal()} := by\n  {CLOSERS}"
        if await self.chk.ok(direct_src):
            return {"solved": True, "how": "closers", "proof": direct_src}
        if cfg.get("papers") and not self.lit:
            self.lit = await asyncio.to_thread(papers, self.p.get("informal") or self.goal(), cfg.get("n_papers", 100))
            self.papers = self.lit[:20]
        for arm in cfg["arms"]:
            if time.time() - self.t0 > cfg["max_seconds"]:
                break
            if arm == "direct":
                src = await self.direct(cfg.get("direct_attempts", 2))
                g = None
            elif arm == "sketch":
                src = await self.sketch(cfg.get("sketch_attempts", 2)); g = None
            else:
                src, g = await self.bracket()
            if src:
                import connect as C
                C.learn_hints(src)
                return {"solved": True, "how": arm, "generation": g, "proof": src}
        return {"solved": False}


INLINE = """Lean 4 + Mathlib. Rewrite this as ONE theorem `{name}` with the same statement, at most {lim} tactic lines
(heavy automation like nlinarith/aesop counts as 3). No sorry. Return only the full theorem in one ```lean block.
```lean
{src}
```"""

FRESH = """Lean 4 + Mathlib. Give the SHORTEST proof you can of:
theorem {name} {ctx} : {goal} := by
Do not explain. Return only the full theorem in one ```lean block."""


async def compress(run, src):
    p, chk = run.p, run.chk
    hist = [("found", wsteps(src))]; best = src

    async def better(cand):
        nonlocal best
        if cand and f"theorem {p['name']}" in cand and wsteps(cand) < wsteps(best) and await chk.ok(cand):
            best = cand; return True
        return False
    for _ in range(3):
        s2 = await chk.simplify(best)
        if s2 == best or not await better(s2):
            break
    hist.append(("simplify", wsteps(best)))
    await better(f"theorem {p['name']} {p['ctx']} : {p['goal']} := by\n  {CLOSERS}")
    hist.append(("one closer", wsteps(best)))
    for _ in range(run.cfg.get("fresh_tries", 3)):  # re-prove from scratch, statement only (idea 23)
        c = lean_block(await run.say_a(FRESH.format(name=p["name"], ctx=p["ctx"], goal=p["goal"]), 0.9, 2500))
        await better(c.replace("import Mathlib", "").strip() if c else None)
    hist.append(("fresh re-prove", wsteps(best)))

    async def ladder():
        for cut in (0.8, 0.7, 0.6, 0.5):
            lim = max(1, int(wsteps(best) * (1 - cut)))
            for _ in range(2):
                c = lean_block(await run.say_a(INLINE.format(name=p["name"], lim=lim, src=best), 0.7, 2500))
                if await better(c.replace("import Mathlib", "").strip() if c else None):
                    return cut
        return None
    r1 = await ladder(); hist.append(("ladder pass 1", wsteps(best)))
    before2 = wsteps(best); r2 = await ladder(); hist.append(("ladder pass 2", wsteps(best)))
    return best, {"history": hist, "rungs": [r1, r2], "pass2_still_shortened": wsteps(best) < before2}
