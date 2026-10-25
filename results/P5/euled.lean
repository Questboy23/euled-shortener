import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat
namespace IMO2025.P5
lemma round15_lemma1 (l : ℝ) (hl0 : l > 0) (WinA : ℕ → ℝ → ℝ → Prop)
  (winA_iff : ∀ (n : ℕ) (sum1 sum2 : ℝ), WinA n sum1 sum2 ↔
    ∃ a : ℝ, a ≥ 0 ∧ sum1 + a ≤ (2 * n + 1) * l ∧
      ∀ b : ℝ, b ≥ 0 → sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 →
        WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))
  (hl : l > √2 / 2):
  ∀ (k : ℕ) (s1 s2 : ℝ),
    (¬ WinA k s1 s2) →
    (0 ≤ s1) →
    (0 ≤ s2) →
    (s1 ^ 2 ≤ (k : ℝ) * s2) →
    (s2 ≤ 2 * (k : ℝ)) →
    ∃ (b_next : ℝ),
      b_next ≥ 0 ∧
      (¬ WinA (k + 1) (s1 + b_next) (s2 + b_next ^ 2)) ∧
      (s2 + b_next ^ 2 ≤ 2 * ((k : ℝ) + 1)) ∧
      ((s1 + b_next) ^ 2 ≤ ((k : ℝ) + 1) * (s2 + b_next ^ 2)) := by
  intro k s1 s2 hW hs1 hs2 hsq hs2k; have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hl2 : (1:ℝ) / 2 < l ^ 2 := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  rw [winA_iff] at hW; push_neg at hW
  obtain ⟨b, hb, hle, hnw⟩ := hW 0 le_rfl (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 * k + 1) hl0.le, mul_le_mul_of_nonneg_left hl2.le (sq_nonneg (2 * (k:ℝ) + 1)), mul_le_mul_of_nonneg_left hs2k hk])
  refine ⟨b, hb, by simpa using hnw, by linarith [show (0:ℝ) ^ 2 = 0 by norm_num], ?_⟩
  rcases hk.eq_or_lt with h | h
  · rw [← h] at hsq ⊢; obtain rfl : s1 = 0 := (by nlinarith); nlinarith
  · nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ k + 1) (sub_nonneg.2 hsq), sq_nonneg ((k:ℝ) * b - s1)]

lemma round15_h_main (l : ℝ) (hl0 : l > 0) (WinA : ℕ → ℝ → ℝ → Prop)
  (winA_iff : ∀ (n : ℕ) (sum1 sum2 : ℝ), WinA n sum1 sum2 ↔
    ∃ a : ℝ, a ≥ 0 ∧ sum1 + a ≤ (2 * n + 1) * l ∧
      ∀ b : ℝ, b ≥ 0 → sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 →
        WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))
  (hl : l > √2 / 2)
  (h : ¬ WinA 0 0 0)
  (lemma1 : ∀ (k : ℕ) (s1 s2 : ℝ),
    (¬ WinA k s1 s2) →
    (0 ≤ s1) →
    (0 ≤ s2) →
    (s1 ^ 2 ≤ (k : ℝ) * s2) →
    (s2 ≤ 2 * (k : ℝ)) →
    ∃ (b_next : ℝ),
      b_next ≥ 0 ∧
      (¬ WinA (k + 1) (s1 + b_next) (s2 + b_next ^ 2)) ∧
      (s2 + b_next ^ 2 ≤ 2 * ((k : ℝ) + 1)) ∧
      ((s1 + b_next) ^ 2 ≤ ((k : ℝ) + 1) * (s2 + b_next ^ 2))):
  ∀ k : ℕ, ∃ s1 s2 : ℝ, (0 ≤ s1) ∧ (0 ≤ s2) ∧ (s1 ^ 2 ≤ (k : ℝ) * s2) ∧ (s2 ≤ 2 * (k : ℝ)) ∧ (¬ WinA k s1 s2) := by
  intro k
  induction k with
  | zero => exact ⟨0, 0, by simp, by simp, by simp, by simp, h⟩
  | succ k ih =>
    obtain ⟨s1, s2, h1, h2, h3, h4, h5⟩ := ih
    obtain ⟨b, hb, hw, hs, hq⟩ := lemma1 k s1 s2 h5 h1 h2 h3 h4
    refine ⟨s1 + b, s2 + b ^ 2, by linarith, add_nonneg h2 (sq_nonneg b), ?_, ?_, hw⟩
    · push_cast; exact hq
    · push_cast; exact hs

theorem imo2025_p5_algebra_A (l : ℝ) (hl0 : l > 0) (WinA : ℕ → ℝ → ℝ → Prop)
    (winA_iff : ∀ (n : ℕ) (sum1 sum2 : ℝ), WinA n sum1 sum2 ↔
      ∃ a : ℝ, a ≥ 0 ∧ sum1 + a ≤ (2 * n + 1) * l ∧
        ∀ b : ℝ, b ≥ 0 → sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 →
          WinA (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))
    (hl : l > √2 / 2) : WinA 0 0 0 := by
  by_contra h
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ (s1 s2 : ℝ), 0 ≤ s1 → s1 ≤ √2 * (N : ℝ) → 0 ≤ s2 → s2 ≤ 2 * (N : ℝ) → s2 + ((2 * (N : ℝ) + 1) * l - s1) ^ 2 > 2 * (N : ℝ) + 2 := by
    obtain ⟨N, hN⟩ := exists_nat_gt (4 / (2 * l - √2) ^ 2 + 1)
    have hc : (0:ℝ) < 2 * l - √2 := by linarith
    have key : (4:ℝ) < N * (2 * l - √2) ^ 2 := (div_lt_iff₀ (pow_pos hc 2)).mp (by linarith)
    have hN1 : (1:ℝ) ≤ N := by linarith [div_nonneg (by norm_num : (0:ℝ) ≤ 4) (sq_nonneg (2 * l - √2))]
    refine ⟨N, fun s1 s2 _ h2 h3 _ => ?_⟩
    have hT : (2 * l - √2) * N ≤ (2 * (N:ℝ) + 1) * l - s1 := by nlinarith [Real.sqrt_nonneg 2]
    have hNa : 0 ≤ (2 * l - √2) * N := mul_nonneg hc.le (Nat.cast_nonneg N)
    nlinarith [mul_le_mul hT hT hNa (le_trans hNa hT), mul_lt_mul_of_pos_left key (by linarith : (0:ℝ) < N)]
  obtain ⟨s1, s2, h1, h2, h3, h4, h5⟩ := round15_h_main l hl0 WinA winA_iff hl h (round15_lemma1 l hl0 WinA winA_iff hl) N
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsq : (√2 * N) ^ 2 = 2 * (N : ℝ) ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have h6 : s1 ≤ √2 * N := by nlinarith [mul_nonneg (Real.sqrt_nonneg 2) hN0, hsq, (by nlinarith [mul_le_mul_of_nonneg_left h4 hN0] : s1 ^ 2 ≤ 2 * (N : ℝ) ^ 2)]
  have h7 := hN s1 s2 h1 h6 h2 h4
  rw [winA_iff] at h5
  push_neg at h5
  obtain ⟨b, _, hb2, _⟩ := h5 ((2 * N + 1) * l - s1) (by nlinarith [mul_nonneg hN0 (show (0 : ℝ) ≤ 2 * l - √2 by linarith)]) (by linarith)
  nlinarith [sq_nonneg b]

lemma round3_P_inductive_step_backward (l : ℝ) (hl0 : l > 0) (hl : l < √2 / 2)
  (WinB : ℕ → ℝ → ℝ → Prop)
  (winB_iff : ∀ (n : ℕ) (sum1 sum2 : ℝ), WinB n sum1 sum2 ↔
    ∀ a : ℝ, a ≥ 0 → sum1 + a ≤ (2 * n + 1) * l →
      ∃ b : ℝ, b ≥ 0 ∧ sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 ∧
        WinB (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))
  (k : ℕ)
  (P_holds_for_k_plus_1 : ∀ (s₁ : ℝ) (s₂ : ℝ), s₁ ≥ ((k + 1 : ℕ) : ℝ) * Real.sqrt 2 → s₂ = 2 * ((k + 1 : ℕ) : ℝ) → WinB (k + 1) s₁ s₂):
  ∀ (s₁ : ℝ) (s₂ : ℝ), s₁ ≥ (k : ℝ) * Real.sqrt 2 → s₂ = 2 * (k : ℝ) → WinB k s₁ s₂ := by
  intro s₁ s₂ h1 h2; rw [winB_iff]; intro a ha hsum
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num); have hs0 := Real.sqrt_nonneg 2
  have hkl := mul_le_mul_of_nonneg_left hl.le (show (0:ℝ) ≤ 2 * k + 1 by positivity)
  have ha2 : a ^ 2 ≤ 2 := by nlinarith [mul_nonneg ha hs0]
  have hb := Real.sq_sqrt (show (0:ℝ) ≤ 2 - a ^ 2 by linarith); have hb0 := Real.sqrt_nonneg (2 - a ^ 2)
  have hab : √2 ≤ a + √(2 - a ^ 2) := by nlinarith [mul_nonneg ha hb0]
  exact ⟨√(2 - a ^ 2), hb0, by linarith, P_holds_for_k_plus_1 _ _ (by push_cast; linarith) (by push_cast; linarith)⟩

theorem imo2025_p5_algebra_B (l : ℝ) (hl0 : l > 0) (WinB : ℕ → ℝ → ℝ → Prop)
    (winB_iff : ∀ (n : ℕ) (sum1 sum2 : ℝ), WinB n sum1 sum2 ↔
      ∀ a : ℝ, a ≥ 0 → sum1 + a ≤ (2 * n + 1) * l →
        ∃ b : ℝ, b ≥ 0 ∧ sum2 + a ^ 2 + b ^ 2 ≤ 2 * n + 2 ∧
          WinB (n + 1) (sum1 + a + b) (sum2 + a ^ 2 + b ^ 2))
    (hl : l < √2 / 2) : WinB 0 0 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (l / (√2 - 2 * l))
  have hP : ∀ s₁ s₂ : ℝ, s₁ ≥ (N : ℝ) * √2 → WinB N s₁ s₂ := fun s₁ s₂ h₁ =>
    (winB_iff N s₁ s₂).2 fun a ha hsum => by
      exfalso; nlinarith [(div_lt_iff₀ (by linarith : (0:ℝ) < √2 - 2 * l)).1 hN]
  have key : ∀ d : ℕ, d ≤ N → ∀ s₁ s₂ : ℝ, s₁ ≥ ((N - d : ℕ) : ℝ) * √2 → s₂ = 2 * ((N - d : ℕ) : ℝ) → WinB (N - d) s₁ s₂ := by
    intro d; induction d with
    | zero => exact fun _ s₁ s₂ h₁ _ => hP s₁ s₂ h₁
    | succ d ih => intro hd s₁ s₂ h₁ h₂; rw [show N - d = N - (d + 1) + 1 by omega] at ih; exact round3_P_inductive_step_backward l hl0 hl WinB winB_iff (N - (d + 1)) (ih (by omega)) s₁ s₂ h₁ h₂
  simpa using key N le_rfl 0 0 (by simp) (by simp)

lemma imo2025_p5_draw1_main (l : ℝ) (hl0 : l > 0) (hl : l = √2 / 2) :
  ∃ sa : (n : ℕ) → (Fin n → ℝ) → ℝ, (∀ i x, sa i x ≥ 0) ∧
    ∀ b : ℕ → ℝ, (∀ i : ℕ, b i ≥ 0) →
    ∀ a : ℕ → ℝ, (∀ i : ℕ, a i = sa i (fun j ↦ b (j : ℕ))) →
      ∀ n : ℕ,
        (∀ k, k < n →
          (∑ i ∈ Finset.range k, (a i + b i)) + a k ≤ (2 * k + 1) * l ∧
          (∑ i ∈ Finset.range k, (a i ^ 2 + b i ^ 2)) + a k ^ 2 + b k ^ 2 ≤ 2 * k + 2) →
        (∑ i ∈ Finset.range n, (a i + b i)) + a n ≤ (2 * n + 1) * l := by
  have hl2 : l ^ 2 = 1 / 2 := by rw [hl, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  refine ⟨fun _ _ => 0, fun _ _ => le_refl _, fun b _ a ha n hyp => ?_⟩
  rcases n with _ | m
  · simp [ha]; linarith
  have hQ : ∑ i ∈ Finset.range m, b i ^ 2 + b m ^ 2 ≤ 2 * (m : ℝ) + 2 := by simpa [ha] using (hyp m (by omega)).2
  have h1 : l * ∑ i ∈ Finset.range (m + 1), b i ≤ m + 1 := by have key : ∀ i ∈ Finset.range (m + 1), 4 * l * b i ≤ b i ^ 2 + 2 := fun i _ => (by nlinarith [sq_nonneg (b i - 2 * l)]); have hs := Finset.sum_le_sum key; rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_range_succ (fun i => b i ^ 2)] at hs; push_cast at hs; linarith
  simp only [ha, zero_add, add_zero, Nat.cast_add, Nat.cast_one]
  nlinarith

theorem imo2025_p5_draw_b (l : ℝ) (hl0 : l > 0) (hl : l = √2 / 2) :
  ∃ sa : (n : ℕ) → (Fin n → ℝ) → ℝ, (∀ i x, sa i x ≥ 0) ∧
    ∀ b : ℕ → ℝ, (∀ i : ℕ, b i ≥ 0) →
    ∀ a : ℕ → ℝ, (∀ i : ℕ, a i = sa i (fun j ↦ b (j : ℕ))) →
      ∀ n : ℕ,
        (∀ k, k < n →
          (∑ i ∈ Finset.range k, (a i + b i)) + a k ≤ (2 * k + 1) * l ∧
          (∑ i ∈ Finset.range k, (a i ^ 2 + b i ^ 2)) + a k ^ 2 + b k ^ 2 ≤ 2 * k + 2) →
        (∑ i ∈ Finset.range n, (a i + b i)) + a n ≤ (2 * n + 1) * l := by
  exact imo2025_p5_draw1_main l hl0 hl

lemma imo2025_p5_draw_a_v22_main (l : ℝ) (hl0 : l > 0) (hl : l = √2 / 2) :
  ∃ sb : (n : ℕ) → (Fin (n + 1) → ℝ) → ℝ, (∀ i x, sb i x ≥ 0) ∧
    ∀ a : ℕ → ℝ, (∀ i : ℕ, a i ≥ 0) →
    ∀ b : ℕ → ℝ, (∀ i : ℕ, b i = sb i (fun j ↦ a (j : ℕ))) →
      ∀ n : ℕ,
        (∀ k, k < n →
          (∑ i ∈ Finset.range k, (a i + b i)) + a k ≤ (2 * k + 1) * l ∧
          (∑ i ∈ Finset.range k, (a i ^ 2 + b i ^ 2)) + a k ^ 2 + b k ^ 2 ≤ 2 * k + 2) →
        (∑ i ∈ Finset.range n, (a i + b i)) + a n ≤ (2 * n + 1) * l →
        (∑ i ∈ Finset.range n, (a i ^ 2 + b i ^ 2)) + a n ^ 2 + b n ^ 2 ≤ 2 * n + 2 := by
  subst hl; refine ⟨fun n f => if f (Fin.last n) ≤ √2 then √2 - f (Fin.last n) else 0, fun i x => (by dsimp only; split_ifs <;> linarith), ?_⟩
  intro a ha b h1 n h2 h3
  have hA : ∀ i, √2 ≤ a i + b i := fun i => by by_cases h : a i ≤ √2 <;> simp [h1 i, h] <;> linarith
  have hS : (n : ℝ) * √2 ≤ ∑ i ∈ Finset.range n, (a i + b i) := by simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.range n) => hA i)
  have hS2 : ∑ i ∈ Finset.range n, (a i ^ 2 + b i ^ 2) ≤ 2 * (n : ℝ) := by rcases n with _ | m <;> [simp; (have := (h2 m (by omega)).2; rw [Finset.sum_range_succ]; push_cast; linarith)]
  have h12 : a n ≤ √2 := by linarith [Real.sqrt_nonneg 2]
  rw [show b n = √2 - a n by simp [h1 n, h12]]; nlinarith [mul_nonneg (ha n) (sub_nonneg.mpr h12), Real.mul_self_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

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
  exact imo2025_p5_draw_a_v22_main l hl0 hl
end IMO2025.P5
