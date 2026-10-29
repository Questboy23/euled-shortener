import asyncio, json
from axle import AxleClient
H = "import Mathlib\nimport Aesop\n\nopen BigOperators Real Nat Topology Rat\n\n"
V = json.load(open("verify.json"))
async def main():
    c = AxleClient(); sem = asyncio.Semaphore(10); still = []
    idx = {}
    for f, i in V["failed"]:
        for l in open("res_" + f):
            r = json.loads(l)
            if r["id"] == i: idx[(f, i)] = r
    async def one(k):
        r = idx[k]
        async with sem:
            for a in range(3):
                try:
                    x = await c.check(content=H + r["proof_after"], environment="lean-4.24.0", timeout_seconds=600); break
                except Exception: x = None; await asyncio.sleep(5)
        if x is None or not x.okay or x.failed_declarations or x.lean_messages.errors: still.append(k)
    await asyncio.gather(*[one(k) for k in idx])
    json.dump({"checked": V["checked"], "failed": still, "method": "15 per file, failures re-checked one per file"}, open("verify.json", "w"), indent=1)
    print("still failing", len(still), still[:10])
asyncio.run(main())
