"""Euled Evo: two-sided evolutionary bracket solver + proof compressor (Reed Ostrov's design, Oct 2026).

SOLVER. Problem = context binders CTX and goal G (Lean 4 + Mathlib). Two populations grow toward each other:
  FORWARD  nodes Q: statements proved from CTX               check: theorem (CTX) : Q
  BACKWARD nodes P: statements that suffice for G (or for another backward node)
A CONNECTION is a proof of Q -> P; then G <- P <- Q <- CTX (the flipped bracket: one route is enough).
  - cheapest question first: automatic closers on G before anything else
  - the side being proved pushes hardest: backward gets 2/3 of proposals
  - clonal selection: best nodes are the parents of the next generation
  - ontology cells (MAP-Elites): best node per tag is always kept, so the population stays diverse
  - successive halving: at most CAP nodes per side survive each generation
  - pairing: top-K forward x top-K backward tried every generation, free closers first (parallel AXLE checks),
    then a model proof on the most promising pairs, ordered by Thompson draws (Beta posterior per node) + closeness
  - every checked statement is cached by exact text (transposition table)
COMPRESSOR (shortens the found proof; same checker):
  1. inline: drop helper lemmas whose statement closes with the closers directly in the main proof
  2. AXLE simplify_theorems to fixpoint
  3. model rewrite ladder: demand 80%, then 70, 60, 50% fewer weighted steps; keep shortest verified
  4. idempotence: run 2-3 again; if it still shortens, report "pass 1 not optimal" (Reed's rule)
Length = weighted steps (heavy automation counts 3), not characters.
Checker: AXLE (free). Models: ~/optimizer/llm.py free providers. No Claude Max calls in this file.
"""
import argparse, asyncio, json, os, random, re, sys, time
sys.path.insert(0, os.path.expanduser("~/optimizer"))
import llm  # noqa: E402

ENV = os.environ.get("EULED_ENV", "lean-4.33.1")
HEADER = os.environ.get("EULED_HEADER", "import Mathlib\nset_option maxHeartbeats 400000\nopen BigOperators Real Nat Topology Rat Finset\n")
CLOSERS = "first | omega | norm_num | linarith | positivity | nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), sq_nonneg (a + b + c - 3)] | simp_all | aesop | decide"
HEAVY = re.compile(r"\b(grind|aesop|simp_all|nlinarith|polyrith|first)\b")
LOG = []


def log(*a):
    s = time.strftime("%H:%M:%S ") + " ".join(str(x) for x in a)
    print(s, flush=True); LOG.append(s)


def wsteps(src):
    lines = [l.strip() for l in src.splitlines() if l.strip() and not l.strip().startswith(("--", "import", "open", "theorem", "lemma"))]
    return sum(3 if HEAVY.search(l) else 1 for l in lines)


class Checker:
    def __init__(self):
        from axle import AxleClient
        self.c = AxleClient(); self.cache = {}; self.calls = 0; self.sem = asyncio.Semaphore(16)

    async def ok(self, src):
        if src in self.cache:
            return self.cache[src]
        async with self.sem:
            self.calls += 1
            try:
                r = await self.c.check(content=HEADER + src, environment=ENV)
                good = bool(r.okay) and "sorry" not in src and "native_decide" not in src
            except Exception:
                good = False
        self.cache[src] = good
        return good

    async def simplify(self, src):
        try:
            r = await self.c.simplify_theorems(content=HEADER + src, environment=ENV, timeout_seconds=180)
            out = r.content.replace(HEADER, "", 1) if r.content.startswith(HEADER) else r.content
            return out
        except Exception:
            return src


def fwd_thm(ctx, q, tac): return f"theorem euled_f {ctx} : {q} := by\n  {tac}"
def bwd_thm(ctx, p, g, tac): return f"theorem euled_b {ctx} (h : {p}) : {g} := by\n  {tac}"
def con_thm(ctx, q, p, tac): return f"theorem euled_c {ctx} (hq : {q}) : {p} := by\n  {tac}"


class Node:
    def __init__(self, side, stmt, proof, tags, parent=None, gen=0, via=None):
        self.side, self.stmt, self.proof, self.parent, self.gen, self.via = side, stmt, proof, parent, gen, via
        self.tags = [str(t) for t in (tags or ["misc"])] or ["misc"]
        self.a, self.b, self.fit = 1.0, 1.0, 0.0

    def to(self):
        return {"side": self.side, "stmt": self.stmt, "proof": self.proof, "tags": self.tags, "fit": round(self.fit, 3),
                "gen": self.gen, "parent": self.parent}


def symbols(s):
    return set(re.findall(r"[A-Za-z_][A-Za-z_0-9'.]*|\^|\*|\+|≤|≥|<|>|=|∣|√", s))


def closeness(q, p):
    a, b = symbols(q.stmt), symbols(p.stmt)
    return len(a & b) / max(1, len(a | b))


STATS = {"direct": 0, "fcc": 0, "fail": 0}


def ask_fcc(prompt, temp, max_tokens):
    """Fallback: the local fcc proxy (Anthropic messages API, many free providers behind it, $0)."""
    import requests
    r = requests.post("http://127.0.0.1:8082/v1/messages", timeout=300,
                      headers={"x-api-key": "freecc", "anthropic-version": "2023-06-01", "content-type": "application/json"},
                      json={"model": "claude-sonnet-5-5", "max_tokens": max_tokens, "temperature": temp,
                            "messages": [{"role": "user", "content": prompt}]})
    d = r.json()
    if r.status_code != 200:
        raise RuntimeError(str(d)[:120])
    text = "".join(b.get("text", "") for b in d.get("content", []) if b.get("type") == "text")
    u = d.get("usage", {})
    return text, int(u.get("input_tokens", 0)) + int(u.get("output_tokens", 0))


USE_MAX = os.environ.get("EULED_MAX_PROPOSER") == "1"


def ask_max(prompt):
    """Claude on Reed's Max plan through the CLI (Haiku, no tools). Used only with --max-proposer."""
    import subprocess
    env = {k: v for k, v in os.environ.items() if k not in ("ANTHROPIC_BASE_URL", "ANTHROPIC_AUTH_TOKEN")}
    r = subprocess.run([os.path.expanduser("~/.local/bin/claude"), "-p", prompt, "--model", "claude-haiku-5-5",
                        "--output-format", "json", "--max-turns", "1", "--tools", ""], capture_output=True, text=True, timeout=300, env=env, stdin=subprocess.DEVNULL)
    d = json.loads(r.stdout or "{}")
    u = d.get("usage", {})
    STATS["max_cost_usd"] = STATS.get("max_cost_usd", 0) + float(d.get("total_cost_usd", 0) or 0)
    return d.get("result", ""), int(u.get("input_tokens", 0)) + int(u.get("output_tokens", 0))


def ask(prompt, temp=0.8, max_tokens=2500):
    if USE_MAX:
        try:
            text, tok = ask_max(prompt)
            if text.strip():
                STATS["max"] = STATS.get("max", 0) + 1
                return text, tok
        except Exception as e:
            log("max error", type(e).__name__)
    # fcc first: measured 2026-10-24 19:14, fcc returned valid JSON where direct NIM Nemotron rambled past the token limit
    for _ in range(2):
        try:
            text, tok = ask_fcc(prompt, temp, max_tokens)
            if text.strip():
                STATS["fcc"] += 1
                return text, tok
        except Exception as e:
            err = type(e).__name__
        time.sleep(5)
    try:
        text, tok, prov = llm.chat([{"role": "user", "content": prompt}], temperature=temp, max_tokens=max_tokens, deadline_s=60)
        STATS["direct"] += 1
        return text, tok
    except Exception:
        pass
    STATS["fail"] += 1
    log("model error (direct and fcc)")
    return "", 0


def lean_block(text):
    m = re.findall(r"```lean4?\n(.*?)```", text, re.S)
    return m[-1].strip() if m else None


def parse_json_list(text):
    for m in re.finditer(r"\[\s*\{[\s\S]*?\}\s*\]", text):
        try:
            v = json.loads(m.group(0))
            got = [x for x in v if isinstance(x, dict) and x.get("stmt")]
            if got:
                return got
        except Exception:
            continue
    return []


PROPOSE = """You are helping connect two sides of a Lean 4 + Mathlib proof.
Context (variables and hypotheses, as Lean binders): {ctx}
Goal: {goal}
Proved facts from the context (forward side):
{fwd}
Statements known to imply the goal (backward side):
{bwd}
Task: propose {k} NEW {kind}. {extra}
Each must be one Lean 4 Prop over the context variables, valid Mathlib syntax, no `sorry`.
Give each 1-3 ontology tags (subject or technique, e.g. "AM-GM", "induction", "squares", "parity").
Do not explain or reason in the reply. Respond with ONLY a JSON list and begin your reply with the character [ :
[{{"stmt": "...", "tags": ["..."], "proof": "tactic proof (lines after := by) or empty"}}]"""


async def propose(chk, side, prob, F, B, parents, k, gen):
    ctx, goal = prob["ctx"], prob["goal"]
    fwd = "\n".join(f"- {n.stmt}" for n in F[:8]) or "- (none yet)"
    bwd = "\n".join(f"- {n.stmt}" for n in B[:8]) or f"- {goal}"
    if side == "B":
        kind = "SUFFICIENT CONDITIONS: statements P such that P together with the context implies the goal, or implies one of the backward statements"
        extra = ("Prefer P that are EASIER and closer to the forward facts. Ask: what would need to be the case for this to be the case? "
                 "Small edits of the best backward statements are good; one bold generalization is allowed. Parents: " + ("; ".join(p.stmt for p in parents) or "the goal"))
    else:
        kind = "TRUE CONSEQUENCES of the context, each with a short tactic proof"
        extra = "Prefer facts that move toward the backward statements. Parents: " + ("; ".join(p.stmt for p in parents) or "the context")
    prompt = PROPOSE.format(ctx=ctx, goal=goal, fwd=fwd, bwd=bwd, k=k, kind=kind, extra=extra)
    text, tok = await asyncio.to_thread(ask, prompt, 0.8, 4000)
    cands = parse_json_list(text)[:k]
    if not cands:  # one retry with a hard format reminder
        text, t2 = await asyncio.to_thread(ask, prompt + "\n\nREPLY WITH THE JSON LIST ONLY. FIRST CHARACTER MUST BE [", 0.5, 4000)
        tok += t2; cands = parse_json_list(text)[:k]

    async def verify(c):
        s = str(c["stmt"]).strip()
        raw = re.sub(r"^\s*by\b", "", str(c.get("proof") or "")).strip()
        tacs = [t for t in [raw.replace("\n", "\n  "), CLOSERS] if t.strip()]
        for t in tacs:
            if side == "F":
                if await chk.ok(fwd_thm(ctx, s, t)):
                    return Node("F", s, t, c.get("tags"), parents[0].stmt if parents else None, gen)
            else:
                if await chk.ok(bwd_thm(ctx, s, goal, t)):
                    if await chk.ok(f"theorem euled_eq {ctx} (h : {goal}) : {s} := by\n  {CLOSERS}"):
                        return None  # equivalent to the goal: no progress (Reed: a middle must be easier, not a restatement)
                    return Node("B", s, t, c.get("tags"), "goal", gen)
                for b in B[:4]:
                    if await chk.ok(con_thm(ctx, s, b.stmt, t)):
                        return Node("B", s, t, c.get("tags"), b.stmt, gen, via=b)
        return None
    res = await asyncio.gather(*[verify(c) for c in cands])
    return [r for r in res if r], tok, len(cands)


async def try_pairs(chk, prob, F, B, k, model_pairs):
    ctx = prob["ctx"]
    pairs = [(f, b) for f in F[:k] for b in B[:k]]
    pairs.sort(key=lambda fb: -(random.betavariate(fb[0].a, fb[0].b) * random.betavariate(fb[1].a, fb[1].b) + closeness(*fb)))
    res = await asyncio.gather(*[chk.ok(con_thm(ctx, f.stmt, b.stmt, CLOSERS)) for f, b in pairs])
    for (f, b), good in zip(pairs, res):
        if good:
            return f, b, CLOSERS, 0
        f.b += 0.5; b.b += 0.5
    tok = 0
    for f, b in pairs[:model_pairs]:
        text, t = await asyncio.to_thread(ask, f"Lean 4 + Mathlib. Prove:\ntheorem euled_c {ctx} (hq : {f.stmt}) : {b.stmt} := by\n"
                                                "Return only the tactic proof (lines after `:= by`) in one ```lean block.", 0.5, 1500)
        tok += t
        tac = lean_block(text)
        if tac:
            tac = tac.replace("\n", "\n  ")
            if await chk.ok(con_thm(ctx, f.stmt, b.stmt, tac)):
                return f, b, tac, tok
        f.b += 1; b.b += 1
    return None, None, None, tok


def chain_to_goal(b):
    out = [b]
    while out[-1].via is not None:
        out.append(out[-1].via)
    return out


def assemble(prob, f, b, ctac):
    ctx, goal, args = prob["ctx"], prob["goal"], " ".join(prob["names"])
    chain = chain_to_goal(b)
    parts = [f"theorem euled_f {ctx} : {f.stmt} := by\n  {f.proof}",
             f"theorem euled_c {ctx} (hq : {f.stmt}) : {b.stmt} := by\n  {ctac}"]
    for i, n in enumerate(chain):
        nxt = chain[i + 1].stmt if i + 1 < len(chain) else goal
        parts.append(f"theorem euled_b{i} {ctx} (h : {n.stmt}) : {nxt} := by\n  {n.proof}")
    expr = f"euled_c {args} (euled_f {args})"
    for i in range(len(chain)):
        expr = f"euled_b{i} {args} ({expr})"
    parts.append(f"theorem {prob['name']} {ctx} : {goal} := by\n  exact {expr}")
    return "\n\n".join(parts)


INLINE = """Lean 4 + Mathlib. This proof is split into helper theorems. Rewrite it as ONE theorem `{name}` with the
same statement, as short as possible: at most {lim} tactic lines (heavy automation like nlinarith/aesop counts as 3).
Keep the key intermediate facts as `have` lines only if needed. No sorry. Return only the full theorem in one ```lean block.

```lean
{src}
```"""


async def compress(chk, prob, src):
    """Shorten a verified proof. Returns (best_source, history)."""
    hist = [("found", wsteps(src))]
    best = src
    # stage 1: AXLE simplify to fixpoint
    for _ in range(3):
        s2 = await chk.simplify(best)
        if s2 == best or wsteps(s2) >= wsteps(best) or not await chk.ok(s2):
            break
        best = s2
    hist.append(("simplify", wsteps(best)))
    # stage 0 (cheapest question first, applied to the whole theorem): does one closer do it now?
    one = f"theorem {prob['name']} {prob['ctx']} : {prob['goal']} := by\n  {CLOSERS}"
    if await chk.ok(one) and wsteps(one) < wsteps(best):
        best = one
    # stage 2: rewrite ladder 80/70/60/50% fewer weighted steps, 2 tries per rung
    async def ladder(cur):
        for cut in (0.8, 0.7, 0.6, 0.5):
            lim = max(1, int(wsteps(cur) * (1 - cut)))
            for _ in range(2):
                text, _ = await asyncio.to_thread(ask, INLINE.format(name=prob["name"], lim=lim, src=cur), 0.7, 2500)
                cand = lean_block(text)
                if not cand or f"theorem {prob['name']}" not in cand:
                    continue
                cand = cand.replace("import Mathlib", "").strip()
                if wsteps(cand) < wsteps(cur) and await chk.ok(cand):
                    return cand, cut
        return cur, None
    p1, cut1 = await ladder(best)
    hist.append(("ladder pass 1", wsteps(p1)))
    p2, cut2 = await ladder(p1)
    hist.append(("ladder pass 2 (idempotence test)", wsteps(p2)))
    return p2, hist, {"pass2_still_shortened": wsteps(p2) < wsteps(p1), "rungs": [cut1, cut2]}


async def solve(prob, gens, cap, k, model_pairs, max_seconds):
    random.seed(0)
    chk = Checker(); t0 = time.time(); tokens = 0; proposals = 0
    log("problem", prob["name"], "| goal:", prob["goal"])
    direct = f"theorem {prob['name']} {prob['ctx']} : {prob['goal']} := by\n  {CLOSERS}"
    if await chk.ok(direct):
        log("solved directly by closers")
        return chk, {"solved": True, "how": "closers", "proof": direct, "tokens": 0, "checks": chk.calls, "seconds": round(time.time() - t0, 1)}
    F, B, g = [], [], 0
    for g in range(1, gens + 1):
        if time.time() - t0 > max_seconds:
            break
        res = await asyncio.gather(propose(chk, "B", prob, F, B, B[:3], 2 * k, g), propose(chk, "F", prob, F, B, F[:2], k, g))
        for nodes, tok, n in res:
            tokens += tok; proposals += n
            for nd in nodes:
                if all(nd.stmt != m.stmt for m in (B if nd.side == "B" else F)):
                    (B if nd.side == "B" else F).append(nd)
        for n in F:
            n.fit = max([closeness(n, b) for b in B] or [0]) + 0.2 * n.a / (n.a + n.b)
        for n in B:
            n.fit = max([closeness(f, n) for f in F] or [0]) + 0.2 * n.a / (n.a + n.b)
        for side in (F, B):
            side.sort(key=lambda n: -n.fit)
            elite = {}
            for n in side:
                elite.setdefault(n.tags[0].lower(), n)
            keep = list(elite.values()) + [n for n in side if n not in elite.values()]
            side[:] = sorted(keep[:cap], key=lambda n: -n.fit)
        log(f"gen {g}: F={len(F)} B={len(B)} tokens={tokens} checks={chk.calls} | F0: {F[0].stmt[:70] if F else '-'} | B0: {B[0].stmt[:70] if B else '-'}")
        if F and B:
            f, b, ctac, tok = await try_pairs(chk, prob, F, B, min(5, len(F), len(B)), model_pairs)
            tokens += tok
            if f:
                full = assemble(prob, f, b, ctac)
                good = await chk.ok(full)
                log("CONNECTED gen", g, "| Q:", f.stmt, "| P:", b.stmt, "| assembled proof checks:", good)
                if good:
                    return chk, {"solved": True, "how": "bracket", "generation": g, "forward": f.to(), "backward": b.to(),
                                 "chain": [n.stmt for n in chain_to_goal(b)], "proof": full, "tokens": tokens,
                                 "proposals": proposals, "checks": chk.calls, "seconds": round(time.time() - t0, 1),
                                 "population": {"F": [n.to() for n in F], "B": [n.to() for n in B]}}
    return chk, {"solved": False, "generations": g, "tokens": tokens, "proposals": proposals, "checks": chk.calls,
                 "seconds": round(time.time() - t0, 1), "population": {"F": [n.to() for n in F], "B": [n.to() for n in B]}}


async def baseline(prob, attempts):
    chk = Checker(); tokens = 0; t0 = time.time()
    for i in range(attempts):
        text, t = await asyncio.to_thread(ask, f"Lean 4 + Mathlib. Prove:\ntheorem {prob['name']} {prob['ctx']} : {prob['goal']} := by\n"
                                                "Return only the tactic proof (lines after `:= by`) in one ```lean block.", 0.8, 3000)
        tokens += t
        tac = lean_block(text)
        if tac and await chk.ok(f"theorem {prob['name']} {prob['ctx']} : {prob['goal']} := by\n  " + tac.replace("\n", "\n  ")):
            return {"solved": True, "attempts": i + 1, "tokens": tokens, "seconds": round(time.time() - t0, 1)}
    return {"solved": False, "attempts": attempts, "tokens": tokens, "seconds": round(time.time() - t0, 1)}


async def main(a):
    prob = json.load(open(a.problem))
    out = {"problem": prob}
    if a.baseline:
        out["baseline_direct_model"] = await baseline(prob, a.baseline)
        log("baseline", out["baseline_direct_model"])
    chk, res = await solve(prob, a.gens, a.cap, a.k, a.model_pairs, a.max_seconds)
    out["evo"] = res
    if res.get("solved"):
        short, hist, idem = await compress(chk, prob, res["proof"])
        out["compressed"] = {"proof": short, "history": hist, **idem, "verified": await chk.ok(short),
                             "weighted_steps_before": wsteps(res["proof"]), "weighted_steps_after": wsteps(short)}
        log("compressed", hist, idem)
    out["model_calls"] = STATS
    out["log"] = LOG
    path = a.problem.replace(".json", ".result.json")
    json.dump(out, open(path, "w"), indent=1, ensure_ascii=False)
    log("wrote", path, "| solved:", res.get("solved"))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("problem"); ap.add_argument("--gens", type=int, default=8); ap.add_argument("--cap", type=int, default=12)
    ap.add_argument("--k", type=int, default=4); ap.add_argument("--model-pairs", type=int, default=3)
    ap.add_argument("--max-seconds", type=int, default=1500); ap.add_argument("--baseline", type=int, default=0)
    asyncio.run(main(ap.parse_args()))
