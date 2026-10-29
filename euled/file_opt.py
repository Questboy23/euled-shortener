"""Optimize every tactic proof in a Lean file for step count, keep each statement byte-identical.
python file_opt.py in.lean out.lean report.json [minimal|clear]"""
import asyncio, json, re, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import stepopt as S

DECL = re.compile(r"^(theorem|lemma)\s", re.M)


def split_file(src):
    """Return (prefix, [decl texts]); a decl runs until the next top-level non-indented line."""
    starts = [m.start() for m in DECL.finditer(src)]
    if not starts:
        return src, [], ""
    pre, decls = src[:starts[0]], []
    for i, a in enumerate(starts):
        b = starts[i + 1] if i + 1 < len(starts) else len(src)
        chunk = src[a:b]
        # stop at the first later top-level line that is not part of the proof
        lines = chunk.split("\n"); cut = len(lines)
        for k in range(1, len(lines)):
            if lines[k] and not lines[k][0].isspace() and not lines[k].startswith(("<;>", "--")):
                cut = k; break
        decls.append(("\n".join(lines[:cut]).rstrip() + "\n", "\n".join(lines[cut:])))
    return pre, decls


async def run(src, mode):
    pre, decls = split_file(src)
    chk = S.Checker(os.environ.get("EULED_STEP_CACHE"))
    out, reports, ctx = pre, [], pre
    for decl, tail in decls:
        rec = {"name": (re.match(r"(?:theorem|lemma)\s+(\S+)", decl) or [None, "?"])[1]}
        if not re.search(r":=\s*by\b", decl):
            rec["skipped"] = "term-mode proof"; new = decl
        else:
            try:
                r, new = await S.optimize(ctx, decl, chk, mode=mode)
                rec.update(r)
                if not r.get("compiles"):
                    new = decl
            except Exception as e:
                rec["error"] = repr(e)[:200]; new = decl
        reports.append(rec)
        out += new + ("\n" + tail if tail.strip() else "\n")
        ctx += new + ("\n" + tail if tail.strip() else "\n")
    # whole-file check: the result must compile as one file
    whole = await chk.c.check(content=out, environment=S.ENV, timeout_seconds=600)
    ok = bool(whole.okay) and not (whole.failed_declarations or [])
    return (out if ok else src), reports, ok


def main():
    src = open(sys.argv[1]).read(); mode = sys.argv[4] if len(sys.argv) > 4 else "minimal"
    out, reports, ok = asyncio.run(run(src, mode))
    open(sys.argv[2], "w").write(out)
    tot_b = sum(r.get("steps_before", 0) for r in reports if "steps_after" in r)
    tot_a = sum(r.get("steps_after", 0) for r in reports if "steps_after" in r)
    json.dump({"mode": mode, "file_compiles": ok, "steps_before": tot_b, "steps_after": tot_a,
               "certified": sum(1 for r in reports if r.get("certified")),
               "declarations": reports}, open(sys.argv[3], "w"), indent=1)


if __name__ == "__main__":
    main()
