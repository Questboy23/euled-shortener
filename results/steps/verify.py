"""Independent re-check: every optimized proof compiled under its original name, 15 per file, no renaming."""
import asyncio, json, glob
from axle import AxleClient
H = "import Mathlib\nimport Aesop\n\nopen BigOperators Real Nat Topology Rat\n\n"
async def main():
    c = AxleClient(); sem = asyncio.Semaphore(8); recs = []
    for f in glob.glob("/home/claude/eopt/res_*.jsonl"):
        for l in open(f):
            r = json.loads(l)
            if r.get("compiles") and "steps_after" in r:
                r["_f"] = f; recs.append(r)
    bad = []
    async def chunk(rs):
        src = H + "\n\n".join(r["proof_after"] for r in rs)
        async with sem:
            x = await c.check(content=src, environment="lean-4.24.0", timeout_seconds=600)
        failed = set(x.failed_declarations or []); errs = x.lean_messages.errors or []
        for r in rs:
            if r["id"] in failed or (errs and not failed) or "sorry" in r["proof_after"] or "native_decide" in r["proof_after"]:
                bad.append((r["_f"].split("res_")[1], r["id"]))
    by = {}
    for r in recs: by.setdefault(r["_f"], []).append(r)
    await asyncio.gather(*[chunk(rs[i:i + 15]) for rs in by.values() for i in range(0, len(rs), 15)])
    json.dump({"checked": len(recs), "failed": bad}, open("/home/claude/eopt/verify.json", "w"), indent=1)
    print(len(recs), "checked;", len(bad), "failed", bad[:10])
asyncio.run(main())
