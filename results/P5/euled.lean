import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat
namespace IMO2025.P5
theorem imo2025_p5_algebra_A (l : ℝ) (hl0 : l > 0) (WinA : ℕ → ℝ → ℝ → Prop)
    (winA_iff : ∀ (n : ℕ) (sum1 sum2 : ℝ), WinA n sum1 sum2 ↔
      ∃ a : ℝ, a ≥ 0 ∧ sum1 + a ≤ (2 * n + 1) * l ∧
        ∀ b : ℝ, b ≥ 0 → sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 →
          WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))
    (hl : l > √2 / 2) : WinA 0 0 0 := by
  by_contra h
  have h2 : (1:ℝ) / 2 < l ^ 2 := by
    nlinarith [Real.sq_sqrt zero_le_two, Real.sqrt_nonneg 2]
  have R : ∀ k : ℕ, ∃ s q : ℝ, s ≤ (2 * k + 1) * l ∧ 4 * l * s ≤ q + 4 * l ^ 2 * k ∧
      q ≤ 2 * k ∧ ¬WinA k s q := by
    intro k
    induction k with
    | zero => exact ⟨0, 0, by simp [hl0.le, h]⟩
    | succ k ih =>
      obtain ⟨s, q, E, I, hq, hW⟩ := ih
      rw [winA_iff] at hW; push_neg at hW
      obtain ⟨b, -, hle, hn⟩ := hW 0 le_rfl (by linarith)
      refine ⟨s + 0 + b, q + 0 ^ 2 + b ^ 2, ?_, ?_, ?_, hn⟩ <;> push_cast <;>
        nlinarith [sq_nonneg (b - 2 * l), mul_le_mul_of_nonneg_left h2.le k.cast_nonneg, hl0]
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (2 * l ^ 2 - 1))
  obtain ⟨s, q, E, I, hq, hW⟩ := R n
  rw [winA_iff] at hW; push_neg at hW
  obtain ⟨b, -, hb, -⟩ := hW ((2 * n + 1) * l - s) (by linarith) (by linarith)
  nlinarith [(div_lt_iff₀ (by linarith)).1 hn, sq_nonneg ((2 * n + 1) * l - s - 2 * l), sq_nonneg b]

theorem imo2025_p5_algebra_B (l : ℝ) (hl0 : l > 0) (WinB : ℕ → ℝ → ℝ → Prop)
    (winB_iff : ∀ (n : ℕ) (sum1 sum2 : ℝ), WinB n sum1 sum2 ↔
      ∀ a : ℝ, a ≥ 0 → sum1 + a ≤ (2 * n + 1) * l →
        ∃ b : ℝ, b ≥ 0 ∧ sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 ∧
          WinB (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))
    (hl : l < √2 / 2) : WinB 0 0 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (l / (√2 - 2 * l))
  have hs := Real.sq_sqrt zero_le_two
  have hd : 0 < √2 - 2 * l := by linarith
  rw [div_lt_iff₀ hd] at hN
  have key : ∀ m n : ℕ, n + m = N → ∀ s t : ℝ, n * √2 ≤ s → t ≤ 2 * n → WinB n s t := by
    intro m
    induction m with
    | zero => intro n hn s t h _; simp at hn; subst hn; rw [winB_iff]; intro a ha hsum; exfalso; nlinarith
    | succ m ih =>
      intro n hn s t h h₂; rw [winB_iff]; intro a ha hsum
      have hl' : a ≤ √2 := by nlinarith [mul_nonneg (Nat.cast_nonneg n) hd.le]
      have := mul_nonneg ha (sub_nonneg.2 hl')
      exact ⟨√2 - a, by linarith, by nlinarith, ih (n + 1) (by omega) _ _ (by push_cast; linarith) (by push_cast; nlinarith)⟩
  exact key N 0 (by omega) 0 0 (by simp) (by simp)

theorem imo2025_p5_draw_b (l : ℝ) (hl0 : l > 0) (hl : l = √2 / 2) :
  ∃ sa : (n : ℕ) → (Fin n → ℝ) → ℝ, (∀ i x, sa i x ≥ 0) ∧
    ∀ b : ℕ → ℝ, (∀ i : ℕ, b i ≥ 0) →
    ∀ a : ℕ → ℝ, (∀ i : ℕ, a i = sa i (fun j ↦ b (j : ℕ))) →
      ∀ n : ℕ,
        (∀ k, k < n →
          (∑ i ∈ Finset.range k, (a i + b i)) + a k ≤ (2 * k + 1) * l ∧
          (∑ i ∈ Finset.range k, (a i ^ 2 + b i ^ 2)) + a k ^ 2 + b k ^ 2 ≤ 2 * k + 2) →
        (∑ i ∈ Finset.range n, (a i + b i)) + a n ≤ (2 * n + 1) * l := by
  have h : l ^ 2 = 1 / 2 := by norm_num [hl, div_pow]
  refine ⟨0, fun _ _ => le_rfl, fun b _ a ha n hyp => ?_⟩
  rcases n with _ | m
  · simp [ha, hl0.le]
  have := (hyp m m.lt_succ_self).2
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.range (m + 1)) =>
    (show 4 * l * b i ≤ b i ^ 2 + 2 by nlinarith [sq_nonneg (b i - 2 * l)])
  simp [ha, Finset.sum_range_succ, ← Finset.mul_sum, Finset.sum_add_distrib] at *
  nlinarith

theorem imo2025_p5_draw_a (l : ℝ) (hl0 : l > 0) (hl : l = √2 / 2) :
  ∃ sb : (n : ℕ) → (Fin (n + 1) → ℝ) → ℝ, (∀ i x, sb i x ≥ 0) ∧
    ∀ a : ℕ → ℝ, (∀ i : ℕ, a i ≥ 0) →
    ∀ b : ℕ → ℝ, (∀ i : ℕ, b i = sb i (fun j ↦ a (j : ℕ))) →
      ∀ n : ℕ,
        (∀ k, k < n →
          (∑ i ∈ Finset.range k, (a i + b i)) + a k ≤ (2 * k + 1) * l ∧
          (∑ i ∈ Finset.range k, (a i ^ 2 + b i ^ 2)) + a k ^ 2 + b k ^ 2 ≤ 2 * k + 2) →
        (∑ i ∈ Finset.range n, (a i + b i)) + a n ≤ (2 * n + 1) * l →
        (∑ i ∈ Finset.range n, (a i ^ 2 + b i ^ 2)) + a n ^ 2 + b n ^ 2 ≤ 2 * n + 2 := by
  refine ⟨fun n f => |√2 - f (Fin.last n)|, fun _ _ => abs_nonneg _, fun a ha b hb n h2 h3 => ?_⟩
  subst hl
  simp at hb
  have hS := Finset.sum_le_sum fun i (_ : i ∈ Finset.range n) => (show √2 ≤ a i + b i by linarith [le_abs_self (√2 - a i), hb i])
  simp at hS
  have hS2 : ∑ i ∈ Finset.range n, (a i ^ 2 + b i ^ 2) ≤ 2 * n := by
    rcases n with _ | m <;> simp [Finset.sum_range_succ] <;> linarith [(h2 m (by omega)).2]
  have h12 : 0 ≤ √2 - a n := by linarith
  rw [hb n, sq_abs]
  nlinarith [mul_nonneg (ha n) h12, Real.sq_sqrt zero_le_two]
end IMO2025.P5
