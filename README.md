# Euled: shortens machine-written Lean 4 proofs, 72% to 92% fewer tokens on four IMO 2025 proofs.

**Every shortened file compiles in Lean 4.21 (checked with the third-party [AXLE](https://axle.axiommath.ai) checker) and keeps each competition theorem statement byte-identical to the original.**

The four proofs are ByteDance Seed-Prover's Lean proofs for IMO 2025 problems P1, P3, P4 and P5. Last results update 2026-10-25.

| Problem | Tokens cut, strict count | Tokens cut, their count | Original → Euled tokens (their count) |
|---|---|---|---|
| P1 | 78.7% | 85.9% | 36438 → 5147 |
| P3 | 73.7% | 84.8% | 16341 → 2485 |
| P4 | 71.5% | 84.5% | 29082 → 4497 |
| P5 | 92.2% | 90.4% | 8637 → 825 |

The strict count is the headline because it closes a loophole in the other count (explained below). Result files: `results/P*/euled_strict.lean` and `results/P*/euled.lean`. To check one yourself, paste it into a Lean 4.21 + Mathlib project or into [live.lean-lang.org](https://live.lean-lang.org).

**Try it on your own proof:** [reedsmoneymaker23.com/euled/shorten](https://reedsmoneymaker23.com/euled/shorten/)

## How length is measured

- **Their count** is ProofOptimizer's own `proof_length` function, copied from Appendix L of their paper into [`euled/po_length.py`](euled/po_length.py). It counts Lean tokens: each name, number or symbol is one token. It ignores comments and each declaration's statement. Run on the untouched Seed-Prover files, it reproduces the original lengths in the ProofOptimizer paper within 0.3% (P5: 8,637 against 8,658).
- **Strict count** also counts every helper lemma's statement, leaving only the competition theorems' statements free. Under their count, moving work into a new lemma's statement costs nothing. The strict count closes that loophole. Euled is optimized against the strict count.

## Rules each result follows

1. Each file compiles against Lean 4.21 and Mathlib, checked by [AXLE](https://axle.axiommath.ai).
2. Each competition theorem statement (`theorem imo2025_…`) is byte-identical to Seed-Prover's. Helper lemmas may be rewritten, merged or deleted.
3. No `sorry` and no `native_decide`.
4. The starting point is Seed-Prover's file with comments removed and one Mathlib rename per file (Lean 4.14 to 4.21). Each rename was the file's only compile error.

To check a result yourself, paste `results/P5/euled.lean` into any Lean 4.21 + Mathlib project, or into [live.lean-lang.org](https://live.lean-lang.org).

## How Euled shortens a proof

1. **Per-lemma rewriting** (`compress_long.py`). For each declaration, it tries one automatic tactic, a "shorter by 50% / 70%" rewrite, and a fresh proof from the statement alone. Every candidate is compiled with the whole file. It deletes lemmas nothing uses, and it repeats passes until a pass gains nothing: if a second pass still shortens the proof, the first was not optimal.
2. **Meta-optimizer** (`compress_meta.py`). A bandit picks among 7 operators by tokens saved per Lean check. A bandit is an algorithm that gives more turns to whichever option has paid off best so far. The 7 operators:
   - dead-step deletion
   - proof-state skip edges (jump from a middle step straight to the end with one tactic)
   - shortest single closing tactic
   - shared lemmas for facts proved twice
   - folding lemmas used once into their caller
   - a model-proposed "bridging lemma" that makes several lemmas unnecessary
   - fresh proofs
3. **Stretch demand.** When a round saves under 1%, Euled demands a total 10% below its best. It asks the largest declarations for 40% fewer tokens each, then repairs failed attempts with Lean's error messages for up to 4 tries.
4. **Repeat** (`repeat_run.py`). The whole pipeline runs again on its own output, up to 5 cycles, until a cycle saves under 0.5%.

The models are Claude Haiku plus free models behind a local proxy. Total model spend for P5 was under $0.10.

## Step-count optimizer with certified lower bounds

`euled/stepopt.py` cuts the number of tactic steps in a Lean proof and proves, where it can, that no shorter proof exists over a stated tactic list. It uses no language model, only Lean checks through AXLE.

Study: 439 DeepSeek-Prover-V1.5 miniF2F proofs, of which 256 compile in Lean 4.24 + Mathlib. All numbers below are for those 256.

| Clear mode | Result |
|---|---|
| Total steps | 9640 → 4674 (52% fewer) |
| Median steps per proof | 25.0 → 2.0 |
| Certified optimal over the tactic list | 54% of proofs |

- A step is one tactic invocation.
- The tactic list is 16 generic tactics plus every one-line tactic of the original proof.
- The lower bound comes from compiling every 1-step proof from the list, and every 2-step proof when the list has at most 31 entries. "Certified" means only this: no shorter proof exists over that list.
- Clear mode bans `aesop`, `grind`, `decide`, `tauto` and `simp_all`, so one automation tactic cannot hide a long proof.
- A second "minimal" mode allows those tactics. Its step counts mostly show how much work one automation tactic does, so they are left out of the headline. They are in `results/steps/`.
- Every output was re-checked one proof per file. The 22 that failed that check keep their original proof.

Data and scripts: [`results/steps/`](results/steps/). Write-up: [reedsmoneymaker23.com/euled/steps](https://reedsmoneymaker23.com/euled/steps/). Try it: [reedsmoneymaker23.com/euled/optimize](https://reedsmoneymaker23.com/euled/optimize/).

## Limits

- Four proofs only. Seed-Prover released no Lean proofs for P2 and P6.
- No claim is made against other proof shorteners. ProofOptimizer (Gu et al., arXiv [2510.15700](https://arxiv.org/abs/2510.15700)) reports 43.8% to 53.8% cuts on these four proofs, on its own length count, in Lean 4.14. Euled ran Lean 4.21, where stronger tactics (`grind`, a stronger `omega`) can help, with a different compute budget. A matched comparison has not been run.
- The compile checks were run through AXLE and have not been re-run locally.
- The code imports a local model wrapper (`~/optimizer/llm.py`) that is not in this repo, so the shortening runs cannot be reproduced from this repo alone. The result files can be checked.
- The models are Claude Haiku plus free models behind a local proxy.

## AI disclosure

See `AI_DISCLOSURE.md`.

## Credits

The original proofs are from [ByteDance-Seed/Seed-Prover](https://github.com/ByteDance-Seed/Seed-Prover) (Apache 2.0), commit `38c59ce`. The length metric is from ProofOptimizer (Gu et al., arXiv 2510.15700). Euled is by Reed Ostrov, Denison University.
