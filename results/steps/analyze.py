import json, glob, statistics as st, collections, sys
rows = collections.defaultdict(list)
for f in glob.glob("/home/claude/eopt/res_*.jsonl"):
    split, mode = f.split("res_")[1][:-6].rsplit("_", 1)
    for l in open(f):
        r = json.loads(l); r["split"] = split; rows[mode].append(r)
out = {}
for mode, rs in rows.items():
    ok = [r for r in rs if r.get("compiles") and "steps_after" in r]
    b = [r["steps_before"] for r in ok]; a = [r["steps_after"] for r in ok]
    red = [1 - r["steps_after"] / r["steps_before"] for r in ok if r["steps_before"]]
    cert = [r for r in ok if r.get("certified")]
    def bucket(r):
        if not r.get("lower_bound"): return "no bound"
        g = r["steps_after"] - r["lower_bound"]
        return "0 (optimal)" if g == 0 else "1 to 5" if g <= 5 else "6 to 20" if g <= 20 else "21 to 100" if g <= 100 else "over 100"
    order = ["0 (optimal)", "1 to 5", "6 to 20", "21 to 100", "over 100", "no bound"]
    gaps = collections.Counter(bucket(r) for r in ok)
    one = sum(1 for r in ok if r["steps_after"] == 1)
    big = [r for r in ok if r["steps_before"] >= 20]
    out[mode] = dict(
        attempted=len(rs), compiled=len(ok),
        steps_before_total=sum(b), steps_after_total=sum(a),
        total_step_cut=round(1 - sum(a) / max(1, sum(b)), 3),
        median_before=st.median(b) if b else None, median_after=st.median(a) if a else None,
        mean_per_proof_cut=round(st.mean(red), 3) if red else None,
        chars_cut=round(1 - sum(r["chars_after"] for r in ok) / max(1, sum(r["chars_before"] for r in ok)), 3),
        certified=len(cert), certified_frac=round(len(cert) / max(1, len(ok)), 3),
        one_step=one, one_step_frac=round(one / max(1, len(ok)), 3),
        long_proofs=len(big), long_cut=round(1 - sum(r["steps_after"] for r in big) / max(1, sum(r["steps_before"] for r in big)), 3),
        gap_hist={k: gaps.get(k, 0) for k in order},
        fixpoint_frac=round(sum(1 for r in ok if r.get("fixpoint")) / max(1, len(ok)), 3),
        median_seconds=st.median([r["seconds"] for r in ok]) if ok else None)
json.dump(out, open("/home/claude/eopt/summary.json", "w"), indent=1)
print(json.dumps(out, indent=1))
