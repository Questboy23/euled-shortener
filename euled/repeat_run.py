"""Repeat the whole compression pipeline on one proof until it stops paying: cycle = compress_long (up to 5 passes)
then compress_meta (bandit over 7 operators, rounds until <1%). Cycles repeat up to MAX_CYCLES, stopping early when a
whole cycle saves under 0.5%. Every cycle's file is compiled, statement-locked, and logged to runs/<P>_cycles.jsonl.
Usage: python repeat_run.py P1 [start_file] [first_cycle]
"""
import json, os, re, shutil, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
PROB = sys.argv[1]
os.environ["EULED_PROB"] = PROB
sys.path.insert(0, HERE)
import compress_long as C
import compress_meta as M

MAX_CYCLES = int(os.environ.get("EULED_CYCLES", "5"))
RUN = os.path.join(HERE, "runs")
UV = [os.path.expanduser("~/.local/bin/uv"), "run", "-q", "--no-project", "--with", "axiom-axle", "--with", "requests", "--with", "tiktoken", "python"]


def base_text():
    orig = C.port(open(C.SRC).read())
    return "\n".join(l for l in C.strip_comments(orig).splitlines() if not l.startswith("#print")) + "\n"


def log(msg):
    line = f"{time.strftime('%H:%M:%S')} [{PROB}] {msg}"
    print(line, flush=True)


def run(args, env):
    e = dict(os.environ); e.update(env)
    r = subprocess.run(UV + args, cwd=HERE, env=e, capture_output=True, text=True)
    open(os.path.join(RUN, f"{PROB}_subprocess.log"), "a").write(r.stdout[-20000:] + r.stderr[-5000:])
    return r.returncode


def main():
    base = base_text()
    os_, ol = M.po(base), M.loose(base)
    log(f"original strict {os_}, loose {ol} (paper original {M.ORIG[PROB]}, ProofOptimizer {M.POPT[PROB]} = {100 * (1 - M.POPT[PROB] / M.ORIG[PROB]):.1f}%)")
    prev = sys.argv[2] if len(sys.argv) > 2 else None
    first = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    env = {"EULED_PROB": PROB, "EULED_ORIG_STRICT": str(os_), "EULED_ORIG_LOOSE": str(ol), "EULED_SEM": os.environ.get("EULED_SEM", "6"),
           "EULED_MAX_BUDGET": "15", "EULED_META_CHECKS": os.environ.get("EULED_META_CHECKS", "1500")}
    last = M.po(open(prev).read()) if prev else os_
    for cyc in range(first, MAX_CYCLES + 1):
        t0 = time.time()
        e = dict(env)
        if prev:
            e["EULED_IN"] = prev
        rc1 = run(["compress_long.py"], e)
        short = os.path.join(RUN, f"{PROB}_short.lean")
        if rc1 != 0 or not os.path.exists(short):
            log(f"cycle {cyc}: compress_long failed rc={rc1}; see {PROB}_subprocess.log")
            if not prev:
                return
            shutil.copy(prev, short)
        rc2 = run(["compress_meta.py", short], e)
        out = os.path.join(RUN, f"{PROB}_meta.lean")
        if rc2 != 0 or not os.path.exists(out) or M.po(open(out).read()) > M.po(open(short).read()):
            log(f"cycle {cyc}: meta rc={rc2}; keeping compress_long output")
            out = short
        txt = open(out).read()
        assert C.theorems(txt) == C.theorems(base), "statement lock broken"
        keep = os.path.join(RUN, f"{PROB}_cycle{cyc}.lean")
        shutil.copy(out, keep)
        s, l = M.po(txt), M.loose(txt)
        row = {"problem": PROB, "cycle": cyc, "strict": s, "loose": l, "pct_strict": round(100 * (1 - s / os_), 2),
               "pct_loose": round(100 * (1 - l / ol), 2), "proofoptimizer_pct": round(100 * (1 - M.POPT[PROB] / M.ORIG[PROB]), 1),
               "cycle_gain_pct": round(100 * (last - s) / last, 2), "minutes": round((time.time() - t0) / 60, 1), "file": os.path.basename(keep)}
        open(os.path.join(RUN, f"{PROB}_cycles.jsonl"), "a").write(json.dumps(row) + "\n")
        log(f"CYCLE {row}")
        try:  # keep the public repo current after every verified cycle
            subprocess.run([sys.executable, os.path.join(HERE, "publish_results.py")], cwd=HERE, timeout=300)
        except Exception as ex:
            log(f"publish failed: {ex}")
        if (last - s) / last < 0.005:
            log("converged: cycle saved under 0.5%")
            break
        last, prev = s, keep


if __name__ == "__main__":
    main()
