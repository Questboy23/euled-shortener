"""Euled Optimizer core: step-count minimization of Lean 4 tactic proofs with certified lower bounds.

Step = one tactic invocation. A line holding `a <;> b` is 2 steps; `have h : T := by simp` is 2 steps
(the `have` plus `simp`). Continuation lines inside open brackets count 0.

Upper bound: fixpoint search over verified edits (delete one statement; replace the tail of any tactic
block, from any position, with one tactic from the alphabet). Every candidate is compiled by AXLE.
Lower bound: exhaustive search over all proofs of 1 step (and of 2 steps when the alphabet is small)
drawn from the alphabet A = generic closers + every single-line tactic the input proof itself uses.
"Certified optimal over A" means the found proof length equals that lower bound.
"""
import asyncio, json, re, hashlib, os, time

ENV = os.environ.get("EULED_ENV", "lean-4.24.0")
HEARTBEATS = int(os.environ.get("EULED_HB", "200000"))
CHUNK = int(os.environ.get("EULED_CHUNK", "24"))
CONC = int(os.environ.get("EULED_CONC", "8"))

# Generic argument-free tactics. CLEAR mode drops opaque search procedures.
GENERIC_MIN = ["norm_num", "simp", "simp_all", "omega", "linarith", "nlinarith", "positivity", "ring_nf", "ring",
               "field_simp", "decide", "rfl", "tauto", "aesop", "grind", "norm_num [Nat.Prime] at *"]
OPAQUE = {"aesop", "grind", "decide", "tauto", "simp_all"}
BANNED = ("native_decide", "sorry", "admit")
CLEAR_RANK = ["rfl", "positivity", "ring", "norm_num", "linarith", "omega", "field_simp", "ring_nf", "simp", "nlinarith"]
GENERIC_CLEAR = [t for t in GENERIC_MIN if t not in OPAQUE]


# ---------- parsing ----------
def _depth(s):
    d = 0
    for ch in s:
        if ch in "([{⟨": d += 1
        elif ch in ")]}⟩": d -= 1
    return d


def statements(lines):
    """Split body lines into statements: (start, end) line ranges where a statement owns its
    deeper-indented children and its `<;>` / open-bracket continuation lines."""
    out, i, n = [], 0, len(lines)
    while i < n:
        if not lines[i].strip():
            i += 1; continue
        ind = len(lines[i]) - len(lines[i].lstrip()); j = i + 1; depth = _depth(lines[i])
        while j < n:
            s = lines[j]
            if not s.strip(): j += 1; continue
            ji = len(s) - len(s.lstrip())
            if depth > 0 or ji > ind or (ji == ind and s.lstrip().startswith("<;>")):
                depth += _depth(s); j += 1; continue
            break
        out.append((i, j)); i = j
    return out


def blocks(lines):
    """Every tactic block: list of statement ranges sharing one indentation. Top level first."""
    res = []
    def rec(a, b):
        sts = statements(lines[a:b]); sts = [(a + x, a + y) for x, y in sts]
        if sts: res.append(sts)
        for x, y in sts:
            if y - x > 1:
                ind0 = len(lines[x]) - len(lines[x].lstrip())
                k = x + 1
                while k < y and (not lines[k].strip() or lines[k].lstrip().startswith("<;>")
                                 or len(lines[k]) - len(lines[k].lstrip()) <= ind0):
                    k += 1
                if k < y and lines[x].rstrip().endswith("by"):
                    rec(k, y)
                elif k < y and lines[k].lstrip().startswith("·"):
                    pass
    rec(0, len(lines))
    return res


def steps(body):
    n, depth = 0, 0
    for s in body.split("\n"):
        t = s.strip()
        if not t or t.startswith("--"):
            continue
        if depth > 0:
            depth += _depth(s); n += t.count("<;>"); continue
        core = t[3:].strip() if t.startswith("<;>") else t
        k = t.count("<;>") + (0 if t.startswith("<;>") else 1)
        k += len(re.findall(r";(?!>)", core.replace("<;>", "")))
        if re.search(r":=\s*by\s+\S", core) or re.match(r"(have|obtain|suffices|show)\b.*\bby\s+\S", core):
            k += 1  # inline nested tactic after `by`
        n += k; depth += _depth(s)
    return n


def atoms(body):
    """Single-line tactic statements of the proof, reused as alphabet letters."""
    out = []
    for s in body.split("\n"):
        t = s.strip()
        if t.startswith("<;>"): t = t[3:].strip()
        for part in t.split("<;>"):
            p = part.strip()
            if (p and _depth(p) == 0 and not re.match(r"(·|case\b|next\b|calc\b)", p)
                    and " by" not in p and not p.endswith((":=", "by", "with")) and not any(b in p for b in BANNED)):
                out.append(p)
    return out


# ---------- checking ----------
class Checker:
    def __init__(self, cache_path=None):
        from axle import AxleClient
        self.c = AxleClient(); self.sem = asyncio.Semaphore(CONC); self.calls = 0; self.decls = 0
        self.cache_path = cache_path; self.cache = {}
        if cache_path and os.path.exists(cache_path):
            for l in open(cache_path):
                k, v = json.loads(l); self.cache[k] = v

    async def run(self, header, decls):
        """decls: list of full declaration texts. Returns list of bools (compiled, no sorry)."""
        header = re.sub(r"/--(?:(?!-/)[\s\S])*-/\s*$", "", header)
        keys = [hashlib.sha1((ENV + header + d).encode()).hexdigest() for d in decls]
        todo = [i for i, k in enumerate(keys) if k not in self.cache]
        async def one(idx):
            pre = header + f"\nset_option maxHeartbeats {HEARTBEATS}\n\n"
            parts, spans, line = [], {}, pre.count("\n") + 1
            for i in idx:
                d = re.sub(r"^(theorem|lemma)\s+\S+", f"theorem euled_c{i}", decls[i], count=1)
                spans[i] = (line, line + d.count("\n")); parts.append(d); line += d.count("\n") + 2
            src = pre + "\n\n".join(parts)
            async with self.sem:
                self.calls += 1; self.decls += len(idx)
                r = None
                for attempt in range(3):
                    try:
                        r = await self.c.check(content=src, environment=ENV, timeout_seconds=300)
                        break
                    except Exception:
                        await asyncio.sleep(2 + 3 * attempt)
            if r is None:
                return {i: False for i in idx}
            bad = set(r.failed_declarations or [])
            errs = getattr(r.lean_messages, "errors", None) or []
            elines = [int(m.group(1)) for e in errs for m in [re.match(r"-:(\d+):", e)] if m]
            unplaced = len(elines) < len(errs)
            def good(i):
                a, b = spans[i]
                return (not unplaced) and f"euled_c{i}" not in bad and not any(a <= L <= b for L in elines) \
                    and not any(L < spans[min(idx)][0] for L in elines)
            return {i: good(i) for i in idx}
        res = {}
        for part in await asyncio.gather(*[one(todo[k:k + CHUNK]) for k in range(0, len(todo), CHUNK)]):
            res.update(part)
        for i, ok in res.items():
            self.cache[keys[i]] = ok
            if self.cache_path:
                with open(self.cache_path, "a") as f: f.write(json.dumps([keys[i], ok]) + "\n")
        return [self.cache[k] for k in keys]


# ---------- optimizer ----------
def split_decl(decl):
    m = re.search(r":=\s*by\s*\n", decl)
    if not m:
        m2 = re.search(r":=\s*by\s+", decl)
        return decl[:m2.end()].rstrip() + "\n", "  " + decl[m2.end():].strip() + "\n"
    return decl[:m.end()], decl[m.end():]


def candidates(body, alphabet):
    lines = body.rstrip("\n").split("\n"); out = set()
    for blk in blocks(lines):
        for (a, b) in blk:  # delete one statement
            out.add("\n".join(lines[:a] + lines[b:]))
        ind = " " * (len(lines[blk[0][0]]) - len(lines[blk[0][0]].lstrip()))
        end = blk[-1][1]
        for k, (a, _) in enumerate(blk):  # tail of block from statement k -> one tactic
            if end - a <= 1 and k == len(blk) - 1 and steps(lines[a]) <= 1:
                continue
            for t in alphabet:
                out.add("\n".join(lines[:a] + [ind + t] + lines[end:]))
    return [c for c in out if c.strip()]


async def optimize(header, decl, chk, mode="minimal", max_rounds=8, two_step_cap=2000, log=None, start=None, cap=400, deadline=float(os.environ.get('EULED_DEADLINE', '1e9'))):
    t0 = time.time(); head, body = split_decl(decl)
    generic = GENERIC_CLEAR if mode == "clear" else GENERIC_MIN
    own = list(dict.fromkeys(atoms(body)))
    if mode == "clear":
        own = [a for a in own if a.split()[0] not in OPAQUE]
    alphabet = list(dict.fromkeys(generic + own))
    rec = {"mode": mode, "steps_before": steps(body), "alphabet": len(alphabet)}
    ok = (await chk.run(header, [decl]))[0]
    rec["compiles"] = ok
    if not ok:
        return rec, decl
    if mode == "clear" and any(re.search(rf"(^|[\s;>]){re.escape(o)}\b", body) for o in OPAQUE):
        rec["note"] = "input uses opaque tactics; clear mode replaces them only where a clear step works"
    best = body
    # lower bound: exhaustive 1-step, then 2-step if small enough
    one = [f"  {t}\n" for t in alphabet]
    r1 = await chk.run(header, [head + c for c in one])
    hits1 = [alphabet[i] for i, v in enumerate(r1) if v]
    lb, exhausted = 1, 0
    if hits1:
        rank = {t: i for i, t in enumerate(CLEAR_RANK)}
        pick = min(hits1, key=lambda t: (rank.get(t, 50), len(t))) if mode == "clear" else min(hits1, key=len)
        best = f"  {pick}\n"; lb = 1; exhausted = 0
    else:
        lb, exhausted = 2, 1
        if len(alphabet) ** 2 * 2 <= two_step_cap:
            pairs = [(a, b, f"  {a}\n  {b}\n") for a in alphabet for b in alphabet] + \
                    [(a, b, f"  {a} <;> {b}\n") for a in alphabet for b in alphabet]
            r2 = await chk.run(header, [head + p[2] for p in pairs])
            hits2 = [p[2] for p, v in zip(pairs, r2) if v]
            if hits2:
                best = min(hits2, key=len)
            else:
                lb, exhausted = 3, 2
    if start and steps(split_decl(start)[1]) < steps(best):
        best = split_decl(start)[1]
    rounds = 0
    while steps(best) > lb and rounds < max_rounds and time.time() - t0 < deadline:
        rounds += 1
        cands = [c + "\n" for c in candidates(best, alphabet) if steps(c) < steps(best)]
        cands.sort(key=lambda c: (steps(c), len(c)))
        cands = cands[:cap]
        if not cands:
            break
        res = await chk.run(header, [head + c for c in cands])
        good = [c for c, v in zip(cands, res) if v and not any(b in c for b in BANNED)]
        if not good:
            break
        best = min(good, key=lambda c: (steps(c), len(c)))
        if log: log(f"round {rounds}: {steps(best)} steps")
    # fixpoint check: one more pass must gain nothing
    final_gain = 0
    if steps(best) > lb and time.time() - t0 < deadline:
        cands = [c + "\n" for c in candidates(best, alphabet) if steps(c) < steps(best)][:400]
        if cands:
            res = await chk.run(header, [head + c for c in cands])
            final_gain = int(any(res))
    if steps(best) < lb:  # found proof leaves the alphabet: no valid bound
        lb = None
    rec.update(steps_after=steps(best), lower_bound=lb, exhausted_depth=exhausted,
               certified=lb is not None and steps(best) == lb, rounds=rounds, timed_out=time.time() - t0 >= deadline, fixpoint=final_gain == 0 and time.time() - t0 < deadline,
               chars_before=len(body), chars_after=len(best), seconds=round(time.time() - t0, 1))
    return rec, head + best
