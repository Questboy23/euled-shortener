import asyncio, json, sys, os, pandas as pd, time
sys.path.insert(0, os.path.dirname(__file__)); import stepopt as S
split, lo, hi, mode = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
d = pd.read_parquet(f"/home/claude/data/{split}.parquet").iloc[lo:hi]
HEADER = "import Mathlib\nimport Aesop\n\nopen BigOperators Real Nat Topology Rat\n"
out = f"/home/claude/eopt/res_{split}_{mode}.jsonl"; done = set()
if os.path.exists(out): done = {json.loads(l)["id"] for l in open(out)}
async def main():
    chk = S.Checker("/home/claude/eopt/axle_cache.jsonl")
    sem = asyncio.Semaphore(6)
    async def one(r):
        if r.id in done: return
        decl = r.theorem.rstrip() + "\n" + r.proof.rstrip() + "\n"
        async with sem:
            try:
                rec, best = await S.optimize(HEADER, decl, chk, mode=mode)
            except Exception as e:
                rec, best = {"error": repr(e)[:200]}, decl
        rec["id"] = r.id; rec["proof_after"] = best; rec["proof_before"] = decl
        with open(out, "a") as f: f.write(json.dumps(rec) + "\n")
        print(r.id, {k: rec.get(k) for k in ("compiles","steps_before","steps_after","lower_bound","certified","seconds")}, flush=True)
    await asyncio.gather(*[one(r) for r in d.itertuples()])
    print("axle calls", chk.calls, "decls", chk.decls)
asyncio.run(main())
