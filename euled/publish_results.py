"""Copy the best Lean-verified file per problem into ~/euled-shortener, rebuild the README table, commit and push.
Called after every repeat_run cycle (and by hand). Only files that compiled and kept every competition theorem
statement byte-identical are ever copied (repeat_run checks both before saving a cycle file)."""
import glob, json, os, re, shutil, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.expanduser("~/euled-shortener")
sys.path.insert(0, HERE)
import po_length as P

PAPER = {"P1": (36478, 20506), "P3": (16377, 7907), "P4": (29147, 14531), "P5": (8658, 4002)}
CODE = ["po_length.py", "compress_long.py", "compress_meta.py", "repeat_run.py", "shorten_job.py", "publish_results.py", "euled_evo.py", "euled_evo2.py"]


def decls(t):
    m = re.search(r"^(lemma|theorem)\s", t, re.M)
    t = t[m.start():] if m else t
    return [d for d in re.split(r"\n(?=(?:lemma|theorem)\s)", t) if d.strip() and not d.startswith("#")]


def locked(d):
    return bool(re.match(r"theorem\s+imo\d{4}_", d))


def loose(t):
    return sum(P.proof_length(re.sub(r"\n(end|#print)[^\n]*", "", d)) for d in decls(t))


def strict(t):
    return sum(P.proof_length(d) if locked(d) else len(P.lexer(P.remove_comments(d)).split()) for d in decls(t))


def best_file(p):
    cands = sorted(glob.glob(os.path.join(HERE, "runs", f"{p}_cycle*.lean")))
    cands += glob.glob(os.path.join(HERE, "runs", f"{p}_verified_*.lean"))  # every Lean-verified snapshot
    return min(cands, key=lambda f: loose(open(f).read())) if cands else None


def main(push=True):
    os.makedirs(os.path.join(REPO, "results"), exist_ok=True)
    for f in CODE:
        shutil.copy(os.path.join(HERE, f), os.path.join(REPO, "euled", f))
    rows = []
    for p, (po0, po1) in PAPER.items():
        orig = os.path.join(REPO, "results", p, "original.lean")
        b = best_file(p)
        if not b or not os.path.exists(orig):
            rows.append((p, po0, po1, None, None, None, None)); continue
        os.makedirs(os.path.join(REPO, "results", p), exist_ok=True)
        shutil.copy(b, os.path.join(REPO, "results", p, "euled.lean"))
        o, e = open(orig).read(), open(b).read()
        rows.append((p, po0, po1, loose(o), loose(e), strict(o), strict(e)))
    table = ["| Problem | ProofOptimizer cut | Euled cut (their count) | Euled cut (strict count) | Original → Euled (their count) |", "|---|---|---|---|---|"]
    for p, po0, po1, lo, le, so, se in rows:
        pct_po = 100 * (1 - po1 / po0)
        if lo is None:
            table.append(f"| {p} | {pct_po:.1f}% | running | running | {po0} → running |")
        else:
            win = "**" if 100 * (1 - le / lo) > pct_po else ""
            table.append(f"| {p} | {pct_po:.1f}% | {win}{100 * (1 - le / lo):.1f}%{win} | {100 * (1 - se / so):.1f}% | {lo} → {le} |")
    readme = open(os.path.join(REPO, "README.template.md")).read()
    readme = readme.replace("{{TABLE}}", "\n".join(table)).replace("{{UPDATED}}", time.strftime("%Y-%m-%d %H:%M ET"))
    open(os.path.join(REPO, "README.md"), "w").write(readme)
    json.dump([dict(zip(["problem", "paper_original", "paper_proofoptimizer", "original", "euled", "original_strict", "euled_strict"], r)) for r in rows],
              open(os.path.join(REPO, "results", "results.json"), "w"), indent=1)
    if push:
        subprocess.run("git add -A && git commit -qm 'Update results' -m 'Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>' -m 'Claude-Session: https://claude.ai/code/session_0148dtSFFgR9kBfxedvsYhco' && git push -q", shell=True, cwd=REPO)
    print("\n".join(table))


if __name__ == "__main__":
    main(push="--no-push" not in sys.argv)
