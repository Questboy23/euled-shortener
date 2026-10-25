# Euled beats ProofOptimizer

Euled shortens machine-written Lean 4 proofs. On all four of ByteDance Seed-Prover's IMO 2025 proofs, it cuts more than ProofOptimizer does (Meta FAIR / MIT, ICLR 2026). Across the four proofs combined, ProofOptimizer cut 48.2% and Euled cuts about 83%, measured with ProofOptimizer's own length code. Every Euled file compiles in Lean, and every competition theorem statement is byte-identical to the original.

| Problem | ProofOptimizer cut | Euled cut (their count) | Euled cut (strict count) | Original → Euled (their count) |
|---|---|---|---|---|
| P1 | 43.8% | **83.7%** | 76.5% | 36438 → 5924 |
| P3 | 51.7% | **84.8%** | 73.7% | 16341 → 2485 |
| P4 | 50.1% | **83.0%** | 69.5% | 29082 → 4931 |
| P5 | 53.8% | **81.2%** | 84.7% | 8637 → 1626 |

ProofOptimizer's numbers come from Table 3 of [arXiv 2510.15700](https://arxiv.org/abs/2510.15700). Bold marks a problem where Euled beats ProofOptimizer. Each column shows the best Lean-verified file for that count: `results/P*/euled.lean` for their count, `results/P*/euled_strict.lean` for the strict count. Rows marked "running" are still being compressed. Last updated 2026-10-25 15:04 ET.

**Try it on your own proof:** [reedsmoneymaker23.com/euled/shorten](https://reedsmoneymaker23.com/euled/shorten/)

## How length is measured

- **Their count** is ProofOptimizer's own `proof_length` function, copied from Appendix L of their paper into [`euled/po_length.py`](euled/po_length.py). It counts Lean tokens: each name, number or symbol is one token. It ignores comments and each declaration's statement. Run on the untouched Seed-Prover files, it reproduces the paper's original lengths within 0.3% (P5: 8,637 against 8,658).
- **Strict count** also counts every helper lemma's statement, leaving only the competition theorems' statements free. Under their count, moving work into a new lemma's statement costs nothing. The strict count closes that loophole. Euled is optimized against the strict count and still wins.

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

## Limits

- Results cover only IMO 2025 P1, P3, P4 and P5. Seed-Prover released no Lean proofs for P2 and P6.
- ProofOptimizer ran in Lean 4.14 with an older Mathlib. Euled runs in Lean 4.21, where some tactics (`grind`, a stronger `omega`) can be more powerful, which helps Euled.
- The code imports a local model wrapper (`~/optimizer/llm.py`) that is not in this repo.

## Credits

The original proofs are from [ByteDance-Seed/Seed-Prover](https://github.com/ByteDance-Seed/Seed-Prover) (Apache 2.0), commit `38c59ce`. The length metric is from ProofOptimizer (Gu et al., arXiv 2510.15700). Euled is by Reed Ostrov, Denison University.
