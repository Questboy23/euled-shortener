"""One public shortening job: python shorten_job.py <job_dir>
Reads <job_dir>/in.lean, checks it compiles, runs compress_long (passes until no gain) then compress_meta (capped),
keeps every `theorem` statement fixed, writes <job_dir>/status.json and <job_dir>/out.lean."""
import json, os, re, shutil, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
job = os.path.abspath(sys.argv[1]); jid = os.path.basename(job)
UV = [os.path.expanduser("~/.local/bin/uv"), "run", "-q", "--no-project", "--with", "axiom-axle", "--with", "requests", "--with", "tiktoken", "python"]


def status(**k):
    st = {}
    p = os.path.join(job, "status.json")
    if os.path.exists(p):
        st = json.load(open(p))
    st.update(k); st["updated"] = time.strftime("%Y-%m-%d %H:%M:%S")
    json.dump(st, open(p + ".tmp", "w")); os.replace(p + ".tmp", p)


def main():
    env = dict(os.environ, EULED_PROB=f"job_{jid}", EULED_SRC=os.path.join(job, "in.lean"), EULED_IN=os.path.join(job, "in.lean"),
               EULED_OUT=job, EULED_LOCK="theorem", EULED_ENV=os.environ.get("EULED_ENV", "lean-4.24.0"), EULED_SEM="6",
               EULED_META_CHECKS="400", EULED_MAX_BUDGET="15")
    sys.path.insert(0, HERE); os.environ.update(env)
    import po_length as P
    src = open(os.path.join(job, "in.lean")).read()
    def loose(t):
        return sum(P.proof_length(d) for d in re.split(r"\n(?=(?:lemma|theorem)\s)", t[re.search(r"^(lemma|theorem)\s", t, re.M).start():]) if d.strip())
    if not re.search(r"^(lemma|theorem)\s", src, re.M):
        return status(state="error", error="No top-level `theorem` or `lemma` found.")
    status(state="running", step="checking that your proof compiles", before=loose(src))
    r = subprocess.run(UV + ["compress_long.py"], cwd=HERE, env=env, capture_output=True, text=True, timeout=3600)
    short = os.path.join(job, f"job_{jid}_short.lean")
    if r.returncode != 0 or not os.path.exists(short):
        err = "Your file did not compile in Lean 4.24 + Mathlib." if "port failed" in r.stderr else "Shortening failed."
        return status(state="error", error=err, detail=r.stderr[-600:])
    status(step="searching for shortcuts across the whole proof", after=loose(open(short).read()))
    subprocess.run(UV + ["compress_meta.py", short], cwd=HERE, env=env, capture_output=True, text=True, timeout=3600)
    meta = os.path.join(HERE, "runs", f"job_{jid}_meta.lean")
    best = meta if os.path.exists(meta) and loose(open(meta).read()) < loose(open(short).read()) else short
    shutil.copy(best, os.path.join(job, "out.lean"))
    b, a = loose(src), loose(open(best).read())
    status(state="done", step="done", before=b, after=a, pct=round(100 * (1 - a / b), 1))


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        status(state="error", error=f"{type(e).__name__}: {str(e)[:200]}")
