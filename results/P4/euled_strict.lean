import Mathlib

set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat Classical Polynomial
namespace IMO2025.P4
lemma a0_is_even1_h_lemma1 (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d):
  ∀ n : ℕ, (a n % 2 = 1) → a (n + 1) < a n := by
  intro n hn
  obtain ⟨b, c, d, hbc, hcd, hdN, -, -, ⟨k, hk⟩, -, hsum⟩ := h1 n
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · interval_cases k <;> omega
  nlinarith

lemma a0_is_even1_h_lemma2 (a : ℕ → ℕ)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d):
  (a 0 % 2 = 1) → ∀ n : ℕ, a n % 2 = 1 := by
  intro h0 n
  induction n with
  | zero => exact h0
  | succ k ih =>
    obtain ⟨b, c, d, -, -, -, hb, hc, hd, -, hs⟩ := h1 k; have ho := Nat.odd_iff.mpr ih; rw [hs, ← Nat.odd_iff]; exact ((ho.of_dvd_nat hb).add_odd (ho.of_dvd_nat hc)).add_odd (ho.of_dvd_nat hd)

lemma a0_is_even1_h_main (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d)
  (h_lemma1 : ∀ n : ℕ, (a n % 2 = 1) → a (n + 1) < a n)
  (h_lemma2 : (a 0 % 2 = 1) → ∀ n : ℕ, a n % 2 = 1):
  Even (a 0) := by
  by_contra h
  rw [Nat.even_iff] at h
  have key : ∀ n, a n + n ≤ a 0 := by
    intro n
    induction n with
    | zero => omega
    | succ k ih => have := h_lemma1 k (h_lemma2 (by omega) k); omega
  have := key (a 0 + 1)
  omega

theorem  a0_is_even (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) (h_an_pos : ∀ n, a n > 0) (h_an_prop : ∀ n, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d):
  Even (a 0) := by
  exact a0_is_even1_h_main a hpos h1 (a0_is_even1_h_lemma1 a hpos h1) (a0_is_even1_h_lemma2 a h1)

lemma prop_a0_divisible_by_31_two_divides_a_n (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) :
  ∀ n : ℕ, 2 ∣ a n := by
  suffices H : ∀ m n, a n = m → 2 ∣ a n from fun n => H _ n rfl
  intro m; refine Nat.strong_induction_on m fun m ih n hn => ?_
  obtain ⟨b, c, d, hbc, hcd, hdm, hb, hc, hd, -, hnext⟩ := h1 n
  by_contra hodd; obtain ⟨k, hk⟩ := id hd; have hp := hpos n
  obtain ⟨p, q, r⟩ : ¬ 2 ∣ b ∧ ¬ 2 ∣ c ∧ ¬ 2 ∣ d := ⟨fun h => hodd (h.trans hb), fun h => hodd (h.trans hc), fun h => hodd (h.trans hd)⟩
  have hk3 : 3 ≤ k := by by_contra h; push_neg at h; interval_cases k <;> omega
  have h2 := ih (b + c + d) (by nlinarith) (n + 1) hnext
  grind

lemma exists_first_term_divisible_by_3_h3 (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d):
  ∃ j, 3 ∣ a j := by
  by_contra! hcon
  have key : ∀ n, a (n + 1) < a n := fun n => by
    obtain ⟨b, c, d, hbc, hcd, hda, ⟨r, hr⟩, ⟨q, hq⟩, ⟨p, hp⟩, -, hsum⟩ := h1 n; have h3 := hcon n
    have hd2 : 2 * d ≤ a n := by rw [hp]; rcases p with _ | _ | p <;> nlinarith [Nat.zero_le d]
    have hq4 : 4 ≤ q := by by_contra! h; interval_cases q <;> omega
    have hc4 : 4 * c ≤ a n := by rw [hq]; nlinarith [Nat.zero_le c, hq4]
    omega
  have bound : ∀ n, a n + n ≤ a 0 := fun n => by induction n with | zero => simp | succ k ih => have := key k; omega
  have := bound (a 0); have := hpos (a 0); omega

lemma exists_first_term_divisible_by_3_h4 (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d)
  (h3 : ∃ j, 3 ∣ a j):
  ∃ j, 3 ∣ a j ∧ ∀ i < j, ¬ (3 ∣ a i) := by
  exact ⟨Nat.find h3, Nat.find_spec h3, fun i hi => Nat.find_min h3 hi⟩

theorem exists_first_term_divisible_by_3 (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d): ∃ j, 3 ∣ a j ∧ ∀ i < j, ¬ (3 ∣ a i) := by
  exact exists_first_term_divisible_by_3_h4 a hpos h1 (exists_first_term_divisible_by_3_h3 a hpos h1)

lemma prop_a0_divisible_by_31_h_main (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d)
  (h_lemma1 : ∀ n : ℕ, (a n % 2 = 1) → a (n + 1) < a n)
  (h_lemma2 : (a 0 % 2 = 1) → ∀ n : ℕ, a n % 2 = 1):
  Even (a 0) := by
  by_contra h
  rw [Nat.even_iff] at h
  have h₁ : ∀ n, a n + n ≤ a 0 := fun n => by
    induction n with | zero => simp | succ n ih => have := h_lemma1 n (h_lemma2 (by omega) n); omega
  have := h₁ (a 0 + 1); omega

lemma prop_a0_divisible_by_31_main_contradiction
  (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d)
  (k : ℕ)
  (b : ℕ)
  (c : ℕ)
  (d : ℕ)
  (h9 : b < c)
  (h10 : c < d)
  (h11 : d < a k)
  (h12 : b ∣ a k)
  (h13 : c ∣ a k)
  (h14 : d ∣ a k)
  (h15 : ∀ e : ℕ, e < a k → e ∣ a k → e ≤ b ∨ e = c ∨ e = d)
  (h16 : a (k + 1) = b + c + d)
  (h_3_div_bcd : 3 ∣ b + c + d)
  (h_not_div_3_b : ¬ (3 ∣ b))
  (h_not_div_3_c : ¬ (3 ∣ c))
  (h_not_div_3_d : ¬ (3 ∣ d))
  (h_4_div_ak : ¬ (4 ∣ a k))
  (h_not_div_3_ak : ¬ (3 ∣ a k)):
  False := by
  have h2s : 2 ∣ b + c + d := by rw [← h16]; exact prop_a0_divisible_by_31_two_divides_a_n a hpos h1 (k + 1)
  obtain ⟨t, ht⟩ := h14
  have ht2 : 2 ≤ t := by by_contra! h; interval_cases t <;> omega
  have hd2 : 2 * d ≤ a k := by rw [ht]; nlinarith [Nat.zero_le d]
  obtain ⟨m, hm⟩ := prop_a0_divisible_by_31_two_divides_a_n a hpos h1 k
  have hN : a k = 2 * d := by rcases h15 m (by omega) ⟨2, by omega⟩ with h | h | h <;> omega
  have key : ∀ x, x ∣ a k → x < d → x % 2 = 1 → 2 * x ≤ b ∨ 2 * x = c ∨ 2 * x = d := fun x hx hxd ho =>
    h15 (2 * x) (by omega) (by rw [hN]; exact mul_dvd_mul_left 2 (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (show ¬ 2 ∣ x by omega))) (by rw [← hN]; exact hx)))
  by_cases hb : b % 2 = 0 <;> by_cases hc : c % 2 = 0
  all_goals first | omega | (have := key c h13 (by omega) (by omega); omega) | (have := key b h12 (by omega) (by omega); omega)

lemma prop_a0_divisible_by_31_case_j_gt_0_and_not_4_div_ak (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d)
  (k : ℕ)
  (j : ℕ)
  (hk : j = k + 1)
  (h_not_div_3_ak : ¬ (3 ∣ a k))
  (b : ℕ)
  (c : ℕ)
  (d : ℕ)
  (h9 : b < c)
  (h10 : c < d)
  (h11 : d < a k)
  (h12 : b ∣ a k)
  (h13 : c ∣ a k)
  (h14 : d ∣ a k)
  (h15 : ∀ e : ℕ, e < a k → e ∣ a k → e ≤ b ∨ e = c ∨ e = d)
  (h16 : a (k + 1) = b + c + d)
  (h_3_div_bcd : 3 ∣ b + c + d)
  (h_not_div_3_b : ¬ (3 ∣ b))
  (h_not_div_3_c : ¬ (3 ∣ c))
  (h_not_div_3_d : ¬ (3 ∣ d))
  (h_4_div_ak : ¬ (4 ∣ a k)):
  False := by
  exact prop_a0_divisible_by_31_main_contradiction a hpos h1 k b c d h9 h10 h11 h12 h13 h14 h15 h16
    h_3_div_bcd h_not_div_3_b h_not_div_3_c h_not_div_3_d h_4_div_ak h_not_div_3_ak

lemma prop_a0_divisible_by_31_h_main' (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d)
  (k : ℕ)
  (j : ℕ)
  (hk : j = k + 1)
  (h_not_div_3_ak : ¬ (3 ∣ a k))
  (b : ℕ)
  (c : ℕ)
  (d : ℕ)
  (h9 : b < c)
  (h10 : c < d)
  (h11 : d < a k)
  (h12 : b ∣ a k)
  (h13 : c ∣ a k)
  (h14 : d ∣ a k)
  (h15 : ∀ e : ℕ, e < a k → e ∣ a k → e ≤ b ∨ e = c ∨ e = d)
  (h16 : a (k + 1) = b + c + d)
  (h_3_div_bcd : 3 ∣ b + c + d)
  (h_not_div_3_b : ¬ (3 ∣ b))
  (h_not_div_3_c : ¬ (3 ∣ c))
  (h_not_div_3_d : ¬ (3 ∣ d))
  (h_4_div_ak : 4 ∣ a k):
  False := by
  obtain ⟨t, ht⟩ := h_4_div_ak
  have h1 := h15 (2 * t) (by omega) ⟨2, by omega⟩
  have h2 := h15 t (by omega) ⟨4, by omega⟩
  have hd : d ≤ 2 * t := by
    obtain ⟨e, he⟩ := h14
    have h₂ : 2 ≤ e := by by_contra! h; interval_cases e <;> omega
    linarith [Nat.mul_le_mul (le_refl d) h₂]
  have hc : c ≤ t := by
    obtain ⟨f, hf⟩ := h13
    have h₄ : 4 ≤ f := by by_contra! h; interval_cases f <;> omega
    linarith [Nat.mul_le_mul (le_refl c) h₄]
  omega

lemma prop_a0_divisible_by_31_case_j_gt_0_and_4_div_ak (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d)
  (k : ℕ)
  (j : ℕ)
  (hk : j = k + 1)
  (h_not_div_3_ak : ¬ (3 ∣ a k))
  (b : ℕ)
  (c : ℕ)
  (d : ℕ)
  (h9 : b < c)
  (h10 : c < d)
  (h11 : d < a k)
  (h12 : b ∣ a k)
  (h13 : c ∣ a k)
  (h14 : d ∣ a k)
  (h15 : ∀ e : ℕ, e < a k → e ∣ a k → e ≤ b ∨ e = c ∨ e = d)
  (h16 : a (k + 1) = b + c + d)
  (h_3_div_bcd : 3 ∣ b + c + d)
  (h_not_div_3_b : ¬ (3 ∣ b))
  (h_not_div_3_c : ¬ (3 ∣ c))
  (h_not_div_3_d : ¬ (3 ∣ d))
  (h_4_div_ak : 4 ∣ a k):
  False := by
  exact prop_a0_divisible_by_31_h_main' a hpos h1 k j hk h_not_div_3_ak b c d h9 h10 h11 h12 h13 h14 h15 h16 h_3_div_bcd h_not_div_3_b h_not_div_3_c h_not_div_3_d h_4_div_ak

lemma prop_a0_divisible_by_31_h_contradiction (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d)
  (j : ℕ)
  (hj1 : 3 ∣ a j)
  (hj2 : ∀ i < j, ¬ (3 ∣ a i))
  (h_j_pos : j > 0):
  False := by
  obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  obtain ⟨b, c, d, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h1 k
  have h₁ : ¬(3 ∣ a k) := hj2 k (by omega)
  have h₂ : 3 ∣ b + c + d := by rw [← h16, ← hk]; exact hj1
  have h₃ : ∀ e, e ∣ a k → ¬ 3 ∣ e := fun e he h => h₁ (dvd_trans h he)
  by_cases h₄ : 4 ∣ a k
  · exact prop_a0_divisible_by_31_case_j_gt_0_and_4_div_ak a hpos h1 k j hk h₁ b c d h9 h10 h11 h12 h13 h14 h15 h16 h₂ (h₃ b h12) (h₃ c h13) (h₃ d h14) h₄
  · exact prop_a0_divisible_by_31_case_j_gt_0_and_not_4_div_ak a hpos h1 k j hk h₁ b c d h9 h10 h11 h12 h13 h14 h15 h16 h₂ (h₃ b h12) (h₃ c h13) (h₃ d h14) h₄

theorem prop_a0_divisible_by_3 (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) (h_exists_first_term_div_3 : ∃ j, 3 ∣ a j) : 3 ∣ a 0 := by
  obtain ⟨j, hj1, hj2⟩ := exists_first_term_divisible_by_3 a hpos h1; rcases Nat.eq_zero_or_pos j with rfl | hj; exacts [hj1, (prop_a0_divisible_by_31_h_contradiction a hpos h1 j hj1 hj2 (by omega)).elim]

theorem v2_of_6_not_4_not_5 (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) (x : ℕ) (h_prop : 6 ∣ x ∧ ¬(4 ∣ x) ∧ ¬(5 ∣ x)): padicValNat 2 x = 1 := by
  rw [show x = 2 * (x / 2) by omega, padicValNat.mul (show (2:ℕ) ≠ 0 by norm_num) (show x / 2 ≠ 0 by omega), padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ x / 2 by omega)]
  simp

lemma v2_decreases_if_div_by_121_main_proof (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d)
  (n : ℕ)
  (h_div_12 : 12 ∣ a n)
  (h_div_4 : 4 ∣ a n)
  (h_div_3 : 3 ∣ a n)
  (h_bcd_form : ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧
    (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d ∧
    b = a n / 4 ∧ c = a n / 3 ∧ d = a n / 2):
  padicValNat 2 (a (n+1)) = padicValNat 2 (a n) - 2 := by
  obtain ⟨k, hk⟩ := h_div_12
  have hk0 : k ≠ 0 := by rintro rfl; have := hpos n; omega
  have key : a (n + 1) = 13 * k := by omega
  rw [key, hk, show (12:ℕ) * k = 2 ^ 2 * (3 * k) by ring,
    padicValNat.mul (by norm_num : (2:ℕ) ^ 2 ≠ 0) (by omega : 3 * k ≠ 0),
    padicValNat.mul (by norm_num : (3:ℕ) ≠ 0) hk0, padicValNat.mul (by norm_num : (13:ℕ) ≠ 0) hk0,
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3),
    padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 13)] <;> omega

theorem v2_decreases_if_div_by_12 (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) (n : ℕ) (h_div_12 : 12 ∣ a n) (h_div_4 : 4 ∣ a n) (h_div_3 : 3 ∣ a n) (h_bcd_form : ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧
    (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d ∧
    b = a n / 4 ∧ c = a n / 3 ∧ d = a n / 2):
  padicValNat 2 (a (n+1)) = padicValNat 2 (a n) - 2 := by
  exact v2_decreases_if_div_by_121_main_proof a hpos h1 n h_div_12 h_div_4 h_div_3 h_bcd_form

lemma valuation_of_3_of_sum_of_divisors1_main (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d)
  (x : ℕ)
  (h_div_3 : 3 ∣ x)
  (h_div_4 : 4 ∣ x)
  (h12 : 12 ∣ x):
  padicValNat 3 (x / 2 + x / 3 + x / 4) = padicValNat 3 x - 1 := by
  obtain ⟨k, rfl⟩ := h12
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  rw [show 12 * k / 2 + 12 * k / 3 + 12 * k / 4 = 13 * k by omega, show 12 * k = 3 * (4 * k) by ring, padicValNat.mul (by norm_num : (13:ℕ) ≠ 0) (by omega : k ≠ 0), padicValNat.mul (by norm_num : (3:ℕ) ≠ 0) (by omega : 4 * k ≠ 0), padicValNat.mul (by norm_num : (4:ℕ) ≠ 0) (by omega : k ≠ 0), padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 13), padicValNat.self (by norm_num : 1 < 3), padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 4)]
  omega

theorem valuation_of_3_of_sum_of_divisors (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) (x : ℕ) (h_div_3 : 3 ∣ x) (h_div_4 : 4 ∣ x):
  padicValNat 3 (x / 2 + x / 3 + x / 4) = padicValNat 3 x - 1 := by
  exact valuation_of_3_of_sum_of_divisors1_main a hpos h1 x h_div_3 h_div_4 (by omega)

lemma round1_h_bcd_form (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) (k : ℕ) (h12 : 12 ∣ a k):
  ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a k ∧ b ∣ a k ∧ c ∣ a k ∧ d ∣ a k ∧ (∀ e : ℕ, e < a k → e ∣ a k → e ≤ b ∨ e = c ∨ e = d) ∧ a (k + 1) = b + c + d ∧ b = a k / 4 ∧ c = a k / 3 ∧ d = a k / 2 := by
  obtain ⟨q, hq⟩ := h12; have hp := hpos k
  obtain ⟨b, c, d, hbc, hcd, hdn, hb, hc, hd, hm, hn⟩ := h1 k
  have hd6 : d = 6 * q := by
    refine le_antisymm ?_ (by have := hm (6 * q) (by omega) ⟨2, by omega⟩; omega)
    obtain ⟨t, ht⟩ := hd
    rcases Nat.lt_or_ge t 2 with h | h <;> nlinarith [Nat.zero_le d]
  have hc4 : c = 4 * q := by
    refine le_antisymm ?_ (by have := hm (4 * q) (by omega) ⟨3, by omega⟩; omega)
    obtain ⟨t, ht⟩ := hc
    rcases Nat.lt_or_ge t 3 with h | h <;> nlinarith [Nat.zero_le c]
  have hb3 : b = 3 * q := by
    refine le_antisymm ?_ (by have := hm (3 * q) (by omega) ⟨4, by omega⟩; omega)
    obtain ⟨t, ht⟩ := hb
    rcases Nat.lt_or_ge t 4 with h | h <;> nlinarith [Nat.zero_le b]
  exact ⟨b, c, d, hbc, hcd, hdn, hb, hc, hd, hm, hn, by omega, by omega, by omega⟩

lemma round1_h1_prime (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) :
  ∀ k : ℕ, (∀ i < k, 12 ∣ a i) → padicValNat 2 (a k) = padicValNat 2 (a 0) - 2 * k ∧ padicValNat 3 (a k) = padicValNat 3 (a 0) - k := by
  intro k; induction k with
  | zero => intro _; constructor <;> simp
  | succ k ih =>
    intro h2; obtain ⟨ih2, ih3⟩ := ih fun i hi => h2 i (by omega); have h25 : 12 ∣ a k := h2 k (by omega)
    have hb := round1_h_bcd_form a hpos h1 k h25; have h39 := v2_decreases_if_div_by_12 a hpos h1 k h25 (by omega) (by omega) hb
    have h47 : a (k + 1) = a k / 2 + a k / 3 + a k / 4 := by obtain ⟨b, c, d, -, -, -, -, -, -, -, h35, h36, h37, h38⟩ := hb; omega
    have h41 : padicValNat 3 (a (k + 1)) = padicValNat 3 (a k) - 1 := by rw [h47]; exact valuation_of_3_of_sum_of_divisors a hpos h1 (a k) (by omega) (by omega)
    exact ⟨by omega, by omega⟩

theorem a_k_becomes_6m_form_after_k_steps_of_reduction (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) (k : ℕ): (∀ i < k, 12 ∣ a i) → padicValNat 2 (a k) = padicValNat 2 (a 0) - 2 * k ∧ padicValNat 3 (a k) = padicValNat 3 (a 0) - k := by
  intro h
  exact round1_h1_prime a hpos h1 k h

lemma round1_h_exists_k (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d):
  ∃ k, ¬(12 ∣ a k) := by
  have step : ∀ n, 12 ∣ a n → 12 * a (n + 1) = 13 * a n := by
    intro n h12
    obtain ⟨t, ht⟩ := h12
    obtain ⟨b, c, d, hbc, hcd, hdlt, hbm, hcm, hdm, hmax, hnext⟩ := h1 n
    have hm := hpos n
    have H : ∀ e j : ℕ, e ∣ a n → e * j < a n → e * j + e ≤ a n := by
      intro e j he hej
      obtain ⟨k, hk⟩ := he
      by_contra hc
      push_neg at hc
      have hjk : j < k := by
        by_contra hh
        push_neg at hh
        have := Nat.mul_le_mul_left e hh
        omega
      nlinarith [Nat.mul_le_mul_left e (show j + 1 ≤ k by omega)]
    have ht0 : 0 < t := by omega
    have h6 : 6 * t ∣ a n := ⟨2, by rw [ht]; ring⟩
    have h4 : 4 * t ∣ a n := ⟨3, by rw [ht]; ring⟩
    have h3 : 3 * t ∣ a n := ⟨4, by rw [ht]; ring⟩
    have hd2 := H d 1 hdm (by omega)
    have hd6 : d = 6 * t := by
      have := hmax (6 * t) (by omega) h6
      omega
    have hc4 : c = 4 * t := by
      have hc3 := H c 2 hcm (by omega)
      have := hmax (4 * t) (by omega) h4
      omega
    have hb3 : b = 3 * t := by
      have hb4 := H b 3 hbm (by omega)
      have := hmax (3 * t) (by omega) h3
      omega
    omega
  by_contra hcon
  push_neg at hcon
  have hstep : ∀ n, 12 * a (n + 1) = 13 * a n := fun n => step n (hcon n)
  have hpow : ∀ j n, 12 ^ j ∣ a n := by
    intro j
    induction j with
    | zero => intro n; simp
    | succ j ih =>
      intro n
      have h1' : 12 ^ (j + 1) ∣ 12 * a (n + 1) := by
        rw [pow_succ, mul_comm (12 ^ j) 12]
        exact mul_dvd_mul_left 12 (ih (n + 1))
      rw [hstep n] at h1'
      exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_left _ (by norm_num)) h1'
  have hd := Nat.le_of_dvd (hpos 0) (hpow (a 0) 0)
  have hlt : a 0 < 12 ^ a 0 := Nat.lt_pow_self (by norm_num)
  grind

lemma round1_h_3_div_a0 (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d):
  3 ∣ a 0 := by
  obtain ⟨j, hj, -⟩ := exists_first_term_divisible_by_3 a hpos h1
  exact prop_a0_divisible_by_3 a hpos h1 ⟨j, hj⟩

lemma round1_h_main (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h_3_div_a0 : 3 ∣ a 0)
  (h_a0_pos : a 0 > 0):
  padicValNat 3 (a 0) ≥ 1 := by
  exact one_le_padicValNat_of_dvd (hpos 0) h_3_div_a0

lemma round1_h_a0_even (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d):
  Even (a 0) := by
  apply a0_is_even <;> assumption

lemma round1_h_exists_j_div_3 (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d):
  ∃ j, 3 ∣ a j := by
  exact (exists_first_term_divisible_by_3 a hpos h1).imp fun _ h => h.1

lemma round1_hb (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) : ∀ n : ℕ, 2 ∣ a n := by
  suffices key : ∀ m n, a n ≤ m → 2 ∣ a n from fun n => key (a n) n le_rfl
  intro m; induction m with
  | zero => intro n hn; have := hpos n; omega | succ m ih => intro n hn; by_contra h; obtain ⟨b, c, d, hbc, hcd, hdN, hb, hc, hd, -, hs⟩ := h1 n; obtain ⟨k, hk⟩ := id hd; have h3 : 3 ≤ k := (by rcases k with _ | _ | _ | k <;> omega); have h3d : 3 * d ≤ a n := (by rw [hk]; nlinarith); have hodd : ∀ x, x ∣ a n → ¬ 2 ∣ x := fun x hx h2 => (by have := dvd_trans h2 hx; omega); have := hodd b hb; have := hodd c hc; have := hodd d hd; have := ih (n+1) (by omega); omega

lemma round1_h_2_divides_a_n (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) : ∀ n : ℕ, 2 ∣ a n := by
  exact round1_hb a hpos h1

lemma round1_h_3_div_a0'' (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d)
  (h_exists_j_div_3 : ∃ j, 3 ∣ a j):
  3 ∣ a 0 := by
  exact prop_a0_divisible_by_3 a hpos h1 h_exists_j_div_3

lemma round3_h_main (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) : ∀ n : ℕ, 3 ∣ a n := by
  intro n
  exact round1_h_3_div_a0'' (fun m => a (n + m)) (fun m => hpos (n + m)) (fun m => h1 (n + m)) (round1_h_exists_j_div_3 (fun m => a (n + m)) (fun m => hpos (n + m)) (fun m => h1 (n + m)))

lemma round1_h_3_divides_a_n (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) : ∀ n : ℕ, 3 ∣ a n := by
  exact round3_h_main a hpos h1

lemma exists_first_k_not_divisible_by_12_and_divisible_by_5_main_proof (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) (h_5_div : 5 ∣ a 0) :
  ∃ k, ¬ (12 ∣ a k) ∧ (5 ∣ a k) := by
  by_contra H
  have key : ∀ n, 5 ∣ a n → 12 * a (n + 1) = 13 * a n := fun n h5 => by obtain ⟨s, hs⟩ : 12 ∣ a n := (by by_contra h; exact H ⟨n, h, h5⟩); obtain ⟨b, c, d, hbc, hcd, hdN, ⟨m3, hm3⟩, ⟨m2, hm2⟩, ⟨m1, hm1⟩, hmax, hsucc⟩ := h1 n; have hp := hpos n; have u6 := hmax (6 * s) (by omega) ⟨2, by omega⟩; have u4 := hmax (4 * s) (by omega) ⟨3, by omega⟩; have u3 := hmax (3 * s) (by omega) ⟨4, by omega⟩; have k1 : 2 ≤ m1 := (by by_contra h; push_neg at h; interval_cases m1 <;> omega); have e1 := Nat.mul_le_mul (le_refl d) k1; have k2 : 3 ≤ m2 := (by by_contra h; push_neg at h; interval_cases m2 <;> omega); have e2 := Nat.mul_le_mul (le_refl c) k2; have k3 : 4 ≤ m3 := (by by_contra h; push_neg at h; interval_cases m3 <;> omega); have e3 := Nat.mul_le_mul (le_refl b) k3; omega
  have main : ∀ n, 5 ∣ a n ∧ 12 ^ n * a n = 13 ^ n * a 0 := fun n => by induction n with | zero => exact ⟨h_5_div, by simp⟩ | succ n ih => have k := key n ih.1; refine ⟨by omega, ?_⟩; rw [show 12 ^ (n + 1) * a (n + 1) = 12 ^ n * (12 * a (n + 1)) by ring, k, show 12 ^ n * (13 * a n) = 13 * (12 ^ n * a n) by ring, ih.2]; ring
  have hlt : ∀ m : ℕ, m < 12 ^ m := fun m => by induction m with | zero => norm_num | succ k ih => rw [pow_succ]; omega
  have hd : 12 ^ a 0 ∣ a 0 := (Nat.Coprime.pow (a 0) (a 0) (by norm_num : Nat.Coprime 12 13)).dvd_of_dvd_mul_left ⟨a (a 0), (main (a 0)).2.symm⟩
  have := Nat.le_of_dvd (hpos 0) hd; have := hlt (a 0); omega

theorem exists_first_k_not_divisible_by_12_and_divisible_by_5 (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) (h_5_div : 5 ∣ a 0) :
  ∃ k, ¬ (12 ∣ a k) ∧ (5 ∣ a k) := by
  apply exists_first_k_not_divisible_by_12_and_divisible_by_5_main_proof <;> assumption

lemma if_a_n_is_30k_then_a_n_plus_1_is_odd_main_proof (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d)
  (n k : ℕ) (hk_coprime_2 : Nat.Coprime k 2) (h : a n = 30 * k) :
  Odd (a (n + 1)) := by
  obtain ⟨b, c, d, hbc, hcd, hd, hb, hc, hdv, hmax, hsum⟩ := h1 n
  rw [h] at hd hb hc hdv hmax; have hk0 : 0 < k := (by have := hpos n; omega)
  have hodd : k % 2 = 1 := (by by_contra h2; have := Nat.Coprime.coprime_dvd_left (show 2 ∣ k by omega) hk_coprime_2; norm_num at this)
  have D : ∀ x, x ∣ 30 * k → 6 * k < x → x < 30 * k → x = 10 * k ∨ x = 15 * k := by rintro x ⟨m, hm⟩ h6 hlt; have hm5 : m < 5 := (by nlinarith [Nat.zero_le x]); interval_cases m <;> omega
  have hd15 : d = 15 * k := by rcases hmax (15 * k) (by omega) ⟨2, by omega⟩ with h' | h' | h' <;> have := D d hdv (by omega) hd <;> omega
  have hc10 : c = 10 * k := by rcases hmax (10 * k) (by omega) ⟨3, by omega⟩ with h' | h' | h' <;> have := D c hc (by omega) (by omega) <;> omega
  have hb6 : b = 6 * k := by rcases hmax (6 * k) (by omega) ⟨5, by omega⟩ with h' | h' | h' <;> (by_contra hne; have := D b hb (by omega) (by omega); omega)
  rw [hsum, Nat.odd_iff]; omega

theorem if_a_n_is_30k_then_a_n_plus_1_is_odd (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) (n k : ℕ) (hk_coprime_2 : Nat.Coprime k 2) :
  a n = 30 * k → Odd (a (n+1)) := by
  intro h
  exact if_a_n_is_30k_then_a_n_plus_1_is_odd_main_proof a hpos h1 n k hk_coprime_2 h

lemma round1_h_main_5 (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d):
  ∀ (n : ℕ), ¬ (5 ∣ a n) := by
  intro n h5n
  obtain ⟨k, h12k, h5k⟩ := exists_first_k_not_divisible_by_12_and_divisible_by_5 (fun i => a (n + i)) (fun i => hpos (n + i)) (fun i => h1 (n + i)) (by simpa using h5n)
  obtain ⟨t, ht⟩ : 30 ∣ a (n + k) := by have := round1_h_2_divides_a_n a hpos h1 (n + k); have := round1_h_3_divides_a_n a hpos h1 (n + k); omega
  obtain ⟨r, hr⟩ := if_a_n_is_30k_then_a_n_plus_1_is_odd a hpos h1 (n + k) t (((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm) ht
  obtain ⟨s, hs⟩ := round1_h_2_divides_a_n a hpos h1 (n + k + 1)
  omega

lemma round1_h_final (a : ℕ → ℕ)
  (h_main : ∀ (n : ℕ), ¬ (5 ∣ a n)):
  ¬ (∃ n, 5 ∣ a n) := by
  grind

theorem an_cannot_be_divisible_by_5 (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0) (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) : ¬ (∃ n, 5 ∣ a n) := by
  exact round1_h_final a (round1_h_main_5 a hpos h1)

lemma round1_exists_m (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) :
  ∃ m : ℕ, a 0 = 6 * m ∧ ¬ (5 ∣ m) := by
  obtain ⟨j, hj, -⟩ := exists_first_term_divisible_by_3 a hpos h1
  have h3 := prop_a0_divisible_by_3 a hpos h1 ⟨j, hj⟩
  have h2 := even_iff_two_dvd.mp (a0_is_even a hpos h1 hpos h1)
  obtain ⟨m, hm⟩ : 6 ∣ a 0 := by omega
  exact ⟨m, hm, fun h => an_cannot_be_divisible_by_5 a hpos h1 ⟨0, by rw [hm]; exact h.mul_left 6⟩⟩

lemma round1_h_not_5_div_a0 (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d):
  ¬ (5 ∣ a 0) := by
  obtain ⟨m, h6, hm⟩ := round1_exists_m a hpos h1
  grind

lemma round1_h_main' (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d)
  (h_exists_k : ∃ k, ¬(12 ∣ a k)):
  ∃ k, ¬(12 ∣ a k) ∧ ∀ i < k, 12 ∣ a i := by
  exact ⟨Nat.find h_exists_k, Nat.find_spec h_exists_k, fun i hi => not_not.1 (Nat.find_min h_exists_k hi)⟩

lemma round1_h_padicValNat_5_a0_eq_0 (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) :
  padicValNat 5 (a 0) = 0 := by
  exact padicValNat.eq_zero_of_not_dvd (round1_h_not_5_div_a0 a hpos h1)

lemma round1_h_goal (a : ℕ → ℕ)
  (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d)
  (k : ℕ)
  (h_k_not_12_div : ¬(12 ∣ a k))
  (h_k_prop : ∀ i < k, 12 ∣ a i):
  Odd (padicValNat 2 (a 0)) ∧ padicValNat 2 (a 0) < 2 * padicValNat 3 (a 0) ∧ padicValNat 5 (a 0) = 0 := by
  have h2 := round1_h_2_divides_a_n a hpos h1 k
  have h3 := round1_h_3_divides_a_n a hpos h1 k
  obtain ⟨hr2, hr3⟩ := a_k_becomes_6m_form_after_k_steps_of_reduction a hpos h1 k h_k_prop
  have hv := v2_of_6_not_4_not_5 a hpos h1 (a k) ⟨by omega, by omega, fun h => an_cannot_be_divisible_by_5 a hpos h1 ⟨k, h⟩⟩
  have hpos3 := one_le_padicValNat_of_dvd (by have := hpos k; omega) h3
  exact ⟨⟨k, by omega⟩, by omega, round1_h_padicValNat_5_a0_eq_0 a hpos h1⟩

theorem imo2025_p4_left (a : ℕ → ℕ) (hpos : ∀ n : ℕ, a n > 0)
  (h1 : ∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) : Odd (padicValNat 2 (a 0)) ∧ padicValNat 2 (a 0) < 2 * padicValNat 3 (a 0) ∧ padicValNat 5 (a 0) = 0 := by
  have ⟨k, hk, hk'⟩ := round1_h_main' a hpos h1 (round1_h_exists_k a hpos h1)
  exact round1_h_goal a hpos h1 k hk hk'

lemma imo2025_p4_right8_h1 (a0 k n : ℕ)
  (hn : Nat.Coprime n 10)
  (ha0 : a0 = 6 * 12 ^ k * n):
  n ≥ 1 := by
  exact Nat.pos_of_ne_zero (by rintro rfl; simp at hn)

lemma imo2025_p4_right8_h2 (a0 k n : ℕ)
  (hn : Nat.Coprime n 10)
  (ha0 : a0 = 6 * 12 ^ k * n)
  (h1 : n ≥ 1):
  ∀ m : ℕ, (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) > 0 := by
  intro m
  positivity

lemma imo2025_p4_right8_h3 (a0 k n : ℕ)
  (hn : Nat.Coprime n 10)
  (ha0 : a0 = 6 * 12 ^ k * n)
  (h1 : n ≥ 1)
  (h2 : ∀ m : ℕ, (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) > 0):
  ∀ m : ℕ, (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) > 3 := by
  intro m
  split_ifs <;> nlinarith [Nat.mul_pos (Nat.mul_pos (by positivity : 0 < 12 ^ (k - m)) (by positivity : 0 < 13 ^ m)) h1, Nat.mul_pos (by positivity : 0 < 13 ^ k) h1]

lemma imo2025_p4_right1_main (a0 k n : ℕ)
  (hn : Nat.Coprime n 10)
  (ha0 : a0 = 6 * 12 ^ k * n)
  (h1 : n ≥ 1)
  (h2 : ∀ m : ℕ, (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) > 0)
  (h3 : ∀ m : ℕ, (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) > 3):
  ∀ m : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) ∧
    b ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) ∧
    c ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) ∧
    d ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) ∧
    (∀ e : ℕ, e < (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) →
      e ∣ (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) →
      e ≤ b ∨ e = c ∨ e = d) ∧
    (if (m + 1) ≤ k then 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n else 6 * 13 ^ k * n) =
    b + c + d := by
  intro m; by_cases hm : m + 1 ≤ k
  · obtain ⟨P, hP⟩ : ∃ P, P = 6 * 12 ^ (k - (m + 1)) * 13 ^ m * n := ⟨_, rfl⟩
    have hP0 : 0 < P := by rw [hP]; exact Nat.mul_pos (by positivity) (by omega)
    have e1 : 6 * 12 ^ (k - m) * 13 ^ m * n = 12 * P := by rw [hP, show k - m = (k - (m + 1)) + 1 by omega]; ring
    have e2 : 6 * 12 ^ (k - (m + 1)) * 13 ^ (m + 1) * n = 13 * P := by rw [hP]; ring
    rw [if_pos (by omega : m ≤ k), if_pos hm, e1, e2]
    refine ⟨3 * P, 4 * P, 6 * P, by omega, by omega, by omega, ⟨4, by ring⟩, ⟨3, by ring⟩, ⟨2, by ring⟩, ?_, by ring⟩
    rintro e he ⟨f, hf⟩; rcases Nat.lt_or_ge f 4 with h | h
    · interval_cases f <;> omega
    · have := Nat.mul_le_mul (le_refl e) h; left; linarith
  · have hc : Nat.Coprime (13 ^ k * n) 10 := Nat.Coprime.mul (Nat.Coprime.pow_left k (by norm_num)) hn
    have hN : (if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n) = 6 * (13 ^ k * n) := by split_ifs with h <;> (try rw [show k - m = 0 by omega, show m = k by omega]) <;> ring
    rw [if_neg hm, hN, show 6 * 13 ^ k * n = 6 * (13 ^ k * n) by ring]
    have hQ : 0 < 13 ^ k * n := Nat.mul_pos (by positivity) (by omega)
    generalize 13 ^ k * n = Q at hQ hc ⊢
    have g : Nat.gcd Q 10 = 1 := hc
    have h2 : ¬ 2 ∣ Q := fun h => by have := Nat.dvd_gcd h (by norm_num : 2 ∣ 10); omega
    have h5 : ¬ 5 ∣ Q := fun h => by have := Nat.dvd_gcd h (by norm_num : 5 ∣ 10); omega
    refine ⟨Q, 2 * Q, 3 * Q, by omega, by omega, by omega, ⟨6, by ring⟩, ⟨3, by ring⟩, ⟨2, by ring⟩, ?_, by ring⟩
    rintro e he ⟨f, hf⟩; rcases Nat.lt_or_ge f 6 with h | h
    · interval_cases f <;> omega
    · have := Nat.mul_le_mul (le_refl e) h; left; linarith

theorem imo2025_p4_right (a0 k n : ℕ)
  (hn : Nat.Coprime n 10)
  (ha0 : a0 = 6 * 12 ^ k * n) :
  ∃ a : ℕ → ℕ, (∀ n : ℕ, a n > 0) ∧ (∀ n : ℕ, ∃ b c d : ℕ, b < c ∧ c < d ∧ d < a n ∧ b ∣ a n ∧ c ∣ a n ∧ d ∣ a n ∧ (∀ e : ℕ, e < a n → e ∣ a n → e ≤ b ∨ e = c ∨ e = d) ∧ a (n + 1) = b + c + d) ∧ (a 0 = a0) := by
  have h1 := imo2025_p4_right8_h1 a0 k n hn ha0
  have h2 := imo2025_p4_right8_h2 a0 k n hn ha0 h1
  exact ⟨fun m => if m ≤ k then 6 * 12 ^ (k - m) * 13 ^ m * n else 6 * 13 ^ k * n, h2, imo2025_p4_right1_main a0 k n hn ha0 h1 h2 (imo2025_p4_right8_h3 a0 k n hn ha0 h1 h2), by simp [ha0]⟩
end IMO2025.P4
