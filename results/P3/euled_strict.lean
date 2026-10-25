import Mathlib

set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat Classical Polynomial
namespace IMO2025.P3
lemma round1_h1 (n : ℤ)
  (k : ℕ)
  (hn : n > 0)
  (h_k_le_2_plus_padic : k ≤ 2 + padicValNat 2 n.toNat):
  (2 : ℤ) ^ k ≤ (2 : ℤ) ^ (2 + padicValNat 2 n.toNat) := by
  gcongr <;> norm_num

lemma round1_h2 (n : ℤ)
  (k : ℕ)
  (hn : n > 0):
  (2 : ℤ) ^ (2 + padicValNat 2 n.toNat) = 4 * (2 : ℤ) ^ (padicValNat 2 n.toNat) := by
  ring

lemma round1_h4 (n : ℤ)
  (k : ℕ)
  (hn : n > 0):
  (2 : ℤ) ^ (padicValNat 2 n.toNat) ∣ n := by
  simpa [Int.toNat_of_nonneg hn.le] using Int.natCast_dvd_natCast.mpr (pow_padicValNat_dvd (p := 2) (n := n.toNat))

lemma round1_h5 (n : ℤ)
  (k : ℕ)
  (hn : n > 0)
  (h4 : (2 : ℤ) ^ (padicValNat 2 n.toNat) ∣ n):
  (2 : ℤ) ^ (padicValNat 2 n.toNat) ≤ n := by
  exact Int.le_of_dvd hn h4

lemma round1_h6 (n : ℤ)
  (k : ℕ)
  (hn : n > 0)
  (h5 : (2 : ℤ) ^ (padicValNat 2 n.toNat) ≤ n):
  4 * (2 : ℤ) ^ (padicValNat 2 n.toNat) ≤ 4 * n := by
  linarith

lemma round1_h_main (n : ℤ)
  (f : ℤ → ℤ)
  (k : ℕ)
  (hn : n > 0)
  (hk : f n = (2 : ℤ) ^ k)
  (h7 : (2 : ℤ) ^ k ≤ 4 * n):
  f n ≤ 4 * n := by
  linarith

lemma round1_h6' (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (k : ℕ) (hk : f n = (2 : ℤ) ^ k) (h_k_le_2_plus_padic : k ≤ 2 + padicValNat 2 n.toNat) : f n ≤ 4 * n := by
  rw [hk]
  linarith [round1_h1 n k hn h_k_le_2_plus_padic, round1_h2 n k hn, round1_h5 n k hn (round1_h4 n k hn)]

lemma lte_2_3n_minus_1_lemma1 (k : ℕ) (hk_pos : k > 0) (hk_odd : k % 2 = 1) : padicValNat 2 (3 ^ k - 1) = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := ⟨k / 2, by omega⟩
  have h8 : 3 ^ (2 * n + 1) % 8 = 3 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
  have h1 : 1 ≤ 3 ^ (2 * n + 1) := Nat.one_le_pow _ _ (by norm_num)
  rw [show 3 ^ (2 * n + 1) - 1 = 2 * ((3 ^ (2 * n + 1) - 1) / 2) by omega,
    padicValNat.mul (by norm_num) (by omega), padicValNat_self,
    padicValNat.eq_zero_of_not_dvd (by omega)]

lemma lte_2_3n_minus_1_lemma2 (k : ℕ) (hk_pos : k > 0) (hk_even : k % 2 = 0) : padicValNat 2 (3 ^ k - 1) = 2 + padicValNat 2 k := by
  have h := padicValNat.pow_two_sub_pow (x := 3) (y := 1) (by norm_num) (by norm_num) (by norm_num) (by omega) (Nat.even_iff.mpr hk_even)
  norm_num [show padicValNat 2 4 = 2 by simpa using padicValNat.prime_pow (p := 2) 2, padicValNat_self] at h; omega

theorem lte_2_3n_minus_1 (n : ℤ) (hn : n > 0) : padicValNat 2 (3 ^ n.toNat - 1) = if n % 2 = 1 then 1 else 2 + padicValNat 2 n.toNat := by
  have hpos : n.toNat > 0 := by omega
  have h_main : padicValNat 2 (3 ^ n.toNat - 1) = if n % 2 = 1 then 1 else 2 + padicValNat 2 n.toNat := by
    split_ifs <;>
    (try {
      have h₁ : n.toNat % 2 = 1 := by
        have h₂ : (n.toNat : ℤ) = n := by simp [Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ n)]
        omega
      rw [lte_2_3n_minus_1_lemma1 n.toNat hpos h₁]
    }) <;>
    (try {
      have h₁ : n % 2 = 0 := by omega
      have h₂ : n.toNat % 2 = 0 := by
        have h₃ : (n.toNat : ℤ) = n := by simp [Int.toNat_of_nonneg (by linarith : (0 : ℤ) ≤ n)]
        omega
      rw [lte_2_3n_minus_1_lemma2 n.toNat hpos h₂]
    })
  rw [h_main]

lemma round1_h_k_le_padic (n : ℤ)
  (f : ℤ → ℤ)
  (k : ℕ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (h_2_pow_k_divides : (2 : ℤ) ^ k ∣ 3 ^ n.toNat - 1):
  k ≤ padicValNat 2 (3 ^ n.toNat - 1) := by
  have h4 : 3 ≤ 3 ^ n.toNat := Nat.le_self_pow (by omega) 3
  have h3 : 2 ^ k ∣ 3 ^ n.toNat - 1 := by
    zify [show 1 ≤ 3 ^ n.toNat by omega]
    exact h_2_pow_k_divides
  exact (padicValNat_dvd_iff_le (by omega)).mp h3

lemma round1_main (f : ℤ → ℤ) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) : f 1 = 1 := by
  exact Int.eq_one_of_dvd_one (hpos 1 one_pos).le (by simpa using dvd_add (hf 1 1 one_pos one_pos) (dvd_pow_self (f 1) (show (f 1).toNat ≠ 0 by have := hpos 1 one_pos; omega)))

theorem imo2025_p3_subproblem_f1_is_1_or_f_is_const_1 (f : ℤ → ℤ) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) : (∀ k : ℤ, k > 0 → f k = 1) ∨ f 1 = 1 := by
  right
  exact round1_main f hpos hf

lemma round1_h_subcase1 (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (h_subcase1 : ∀ k : ℤ, k > 0 → f k = k):
  f n ≤ 4 * n := by
  rw [h_subcase1 n hn]
  omega

theorem  f_b_equiv_b_mod_p_of_f_p_ne_1 (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (p : ℤ) (hp : Nat.Prime p.toNat) (hfp_ne_1 : f p ≠ 1):
  ∀ b : ℤ, b > 0 → b ≡ f b [ZMOD p] := by
  intro b hb; have hp0 : (0:ℤ) < p := (by have := hp.two_le; omega); have hfp0 : (0:ℤ) < f p := hpos p hp0; have hfq : f p = ((f p).toNat : ℤ) := (Int.toNat_of_nonneg hfp0.le).symm; have hpq : p = (p.toNat : ℤ) := (Int.toNat_of_nonneg hp0.le).symm
  haveI := Fact.mk hp; haveI : NeZero p.toNat := ⟨hp.ne_zero⟩; have h3 : f p ∣ p ^ p.toNat := (by have := dvd_add (hf p p hp0 hp0) (dvd_pow_self (f p) (by omega : (f p).toNat ≠ 0)); rwa [sub_add_cancel] at this)
  obtain ⟨i, -, hqi⟩ := (Nat.dvd_prime_pow hp).1 (Int.natCast_dvd_natCast.mp (by rw [← hfq, Nat.cast_pow, ← hpq]; exact h3) : (f p).toNat ∣ p.toNat ^ p.toNat)
  have hi0 : i ≠ 0 := by rintro rfl; exact hfp_ne_1 (by have : (f p).toNat = 1 := (by simpa using hqi); omega)
  have hPf : (p.toNat : ℤ) ∣ f p := by rw [hfq]; exact Int.natCast_dvd_natCast.mpr (by rw [hqi]; exact dvd_pow_self _ hi0)
  have key : ((f b : ℤ) : ZMod p.toNat) = (b : ZMod p.toNat) := by have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (hPf.trans (hf p b hp0 hb)); push_cast at hz; rw [sub_eq_zero, ZMod.pow_card, hqi, ZMod.pow_card_pow] at hz; exact hz.symm
  rw [Int.modEq_iff_dvd, hpq, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, key, sub_self]

lemma f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_case2 (f : ℤ → ℤ) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (k : ℤ) (hk_pos : k > 0) (hf_not_id : ∃ i > 0, f i ≠ i) : ∃ p, Nat.Prime p.toNat ∧ p > k ∧ f p = 1 := by
  obtain ⟨i₀, hi₀, hne⟩ := hf_not_id
  by_contra! h
  obtain ⟨q, hqp, hq⟩ := Nat.exists_infinite_primes (k + i₀ + f i₀ + 1).toNat
  have hc : k + i₀ + f i₀ + 1 ≤ (q:ℤ) := le_trans (Int.self_le_toNat _) (by exact_mod_cast hqp)
  have h7 : (q:ℤ) ∣ i₀ - f i₀ := Int.ModEq.dvd (by simpa using (f_b_equiv_b_mod_p_of_f_p_ne_1 (q:ℤ) f (by linarith [hpos i₀ hi₀]) hpos hf (q:ℤ) (by simpa using hq) (h (q:ℤ) (by simpa using hq) (by linarith [hpos i₀ hi₀]))) i₀ hi₀ : i₀ ≡ f i₀ [ZMOD (q:ℤ)]).symm
  exact hne (by linarith [Int.eq_zero_of_abs_lt_dvd h7 (abs_lt.mpr ⟨by linarith [hpos i₀ hi₀], by linarith [hpos i₀ hi₀]⟩)])

lemma f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_case1 (f : ℤ → ℤ) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (k : ℤ) (hk_pos : k > 0) (h11 : ∀ k : ℤ, k > 0 → f k = 1) : ∃ p, Nat.Prime p.toNat ∧ p > k ∧ f p = 1 := by
  obtain ⟨q, hq1, hq2⟩ := Nat.exists_infinite_primes (k.toNat + 1)
  exact ⟨q, by simpa using hq2, by omega, h11 q (by omega)⟩

theorem f_is_not_identity_implies_f_p_eq_1_for_some_p_gt_k (f : ℤ → ℤ) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (k : ℤ) (hk_pos : k > 0) (hf_not_id : ∃ i > 0, f i ≠ i):
  ∃ p, Nat.Prime p.toNat ∧ p > k ∧ f p = 1 := by
  rcases imo2025_p3_subproblem_f1_is_1_or_f_is_const_1 f hpos hf with h11 | _
  exacts [f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_case1 f hpos hf k hk_pos h11, f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_case2 f hpos hf k hk_pos hf_not_id]

lemma f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_h_main (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (h_exists_k : ∃ k : ℤ, k > 1 ∧ f k ≠ k)
  (p0 : ℤ)
  (hp0_prime : Nat.Prime p0.toNat)
  (hfp0_eq_1 : f p0 = 1)
  (h_f_not_const_1 : ∃ n, n > 0 ∧ f n ≠ 1):
  ∀ (p : ℤ), Nat.Prime p.toNat → p ≥ p0 → f p = 1 := by
  intro p hp_prime hp_ge_p0
  by_contra h
  have hp0_two := Nat.Prime.two_le hp0_prime
  have h3 := f_b_equiv_b_mod_p_of_f_p_ne_1 n f hn hpos hf p hp_prime h p0 (by omega)
  rw [hfp0_eq_1] at h3
  have h5 := Int.le_of_dvd (by omega) (Int.modEq_iff_dvd.mp h3.symm)
  omega

theorem f_is_1_on_all_primes_ge_p0_if_f_p0_eq_1_and_f_is_not_const_1 (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (h_exists_k : ∃ k : ℤ, k > 1 ∧ f k ≠ k) {p0 : ℤ} (hp0_prime : Nat.Prime p0.toNat) (hfp0_eq_1 : f p0 = 1) (h_f_not_const_1 : ∃ n, n > 0 ∧ f n ≠ 1): ∀ p, Nat.Prime p.toNat → p ≥ p0 → f p = 1 := by
  exact f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_h_main n f hn hpos hf h_exists_k p0 hp0_prime hfp0_eq_1 h_f_not_const_1

lemma f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_main (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat):
  (∃ n : ℤ, n > 0 ∧ f n ≠ n) → ∀ p : ℤ, Nat.Prime p.toNat → p > 2 → f p = 1 := by
  intro h_f_not_id p hp_prime hp_gt_2; by_contra hfp_ne_1; rcases imo2025_p3_subproblem_f1_is_1_or_f_is_const_1 f hpos hf with h_const | h_f1
  · exact hfp_ne_1 (h_const p (by omega))
  obtain ⟨p0, hp0_prime, hp0_gt_p, hfp0_eq_1⟩ := f_is_not_identity_implies_f_p_eq_1_for_some_p_gt_k f hpos hf p (by omega) h_f_not_id
  have h_exists_k : ∃ k : ℤ, k > 1 ∧ f k ≠ k := by obtain ⟨m, hm0, hfm⟩ := h_f_not_id; rcases (show m = 1 ∨ m > 1 by omega) with rfl | hm; exacts [absurd h_f1 hfm, ⟨m, hm, hfm⟩]
  have h_forall : ∀ q : ℤ, Nat.Prime q.toNat → q ≥ p0 → f q = 1 := f_is_1_on_all_primes_ge_p0_if_f_p0_eq_1_and_f_is_not_const_1 n f hn hpos hf h_exists_k hp0_prime hfp0_eq_1 ⟨p, by omega, hfp_ne_1⟩
  have h_b_equiv := f_b_equiv_b_mod_p_of_f_p_ne_1 n f hn hpos hf p hp_prime hfp_ne_1
  have hpz : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (by omega); haveI : Fact (Nat.Prime p.toNat) := ⟨hp_prime⟩; haveI : NeZero p.toNat := ⟨by omega⟩
  have h2_unit : IsUnit (2 : ZMod p.toNat) := by rw [isUnit_iff_ne_zero]; intro h6; have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_zmod_eq_zero_iff_dvd 2 p.toNat).mp (by exact_mod_cast h6)); omega
  obtain ⟨q, hq1, hq2, hq3⟩ := Nat.forall_exists_prime_gt_and_eq_mod h2_unit p0.toNat
  have h15 : f (q : ℤ) = 1 := h_forall (q : ℤ) (by simpa using hq2) (by omega); have h14 : (q : ℤ) ≡ 1 [ZMOD p] := by have := h_b_equiv (q : ℤ) (by omega); rwa [h15] at this
  have hA : p ∣ (q : ℤ) - 1 := h14.symm.dvd; have hmod : q % p.toNat = 2 % p.toNat := (ZMod.natCast_eq_natCast_iff' q 2 p.toNat).mp (by exact_mod_cast hq3)
  have h8 : p ∣ 1 := by have h7 : p ∣ (q : ℤ) - 2 := (by rw [← hpz, show (q : ℤ) - 2 = ((q - 2 : ℕ) : ℤ) by omega]; exact Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod))); have := dvd_sub hA h7; rwa [show (q : ℤ) - 1 - ((q : ℤ) - 2) = 1 by ring] at this
  have := Int.le_of_dvd (by norm_num) h8; omega

theorem f_is_not_identity_implies_f_p_eq_1_for_p_gt_2 (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat):
  (∃ n : ℤ, n > 0 ∧ f n ≠ n) → ∀ p : ℤ, Nat.Prime p.toNat → p > 2 → f p = 1 := by
  exact f_is_not_identity_implies_f_p_eq_1_for_p_gt_2_main n f hn hpos hf

lemma prime_divisor_of_fa_divides_fx_minus_x_h1 (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (a x p : ℤ)
  (ha : a > 0)
  (hx : x > 0)
  (hp : Nat.Prime p.toNat)
  (hdiv : p ∣ f a):
  p ≥ 2 := by
  have := hp.two_le
  omega

lemma prime_divisor_of_fa_divides_fx_minus_x_h2 (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (a x p : ℤ)
  (ha : a > 0)
  (hx : x > 0)
  (hp : Nat.Prime p.toNat)
  (hdiv : p ∣ f a)
  (h1 : p ≥ 2):
  f p ≠ 1 := by
  intro h
  have h3 := hf a p ha (by omega)
  rw [h, one_pow] at h3
  have h4 : p ≤ 1 := Int.le_of_dvd one_pos (by simpa using dvd_sub (dvd_pow_self p (by omega : a.toNat ≠ 0)) (dvd_trans hdiv h3))
  omega

lemma prime_divisor_of_fa_divides_fx_minus_x_h10 (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (a x p : ℤ)
  (ha : a > 0)
  (hx : x > 0)
  (hp : Nat.Prime p.toNat)
  (hdiv : p ∣ f a)
  (h2 : f p ≠ 1):
  ∀ (b : ℤ), b > 0 → b ≡ f b [ZMOD p] := by
  intro b hb
  apply f_b_equiv_b_mod_p_of_f_p_ne_1 <;> assumption

lemma prime_divisor_of_fa_divides_fx_minus_x_h11 (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (a x p : ℤ)
  (ha : a > 0)
  (hx : x > 0)
  (hp : Nat.Prime p.toNat)
  (hdiv : p ∣ f a)
  (h10 : ∀ (b : ℤ), b > 0 → b ≡ f b [ZMOD p]):
  x ≡ f x [ZMOD p] := by
  exact h10 x hx

lemma prime_divisor_of_fa_divides_fx_minus_x_h13 (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (a x p : ℤ)
  (ha : a > 0)
  (hx : x > 0)
  (hp : Nat.Prime p.toNat)
  (hdiv : p ∣ f a)
  (h11 : x ≡ f x [ZMOD p]):
  p ∣ f x - x := by
  exact h11.dvd

theorem prime_divisor_of_fa_divides_fx_minus_x (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (a x p : ℤ) (ha : a > 0) (hx : x > 0) (hp : Nat.Prime p.toNat) (hdiv : p ∣ f a): p ∣ f x - x := by
  exact prime_divisor_of_fa_divides_fx_minus_x_h13 n f hn hpos hf a x p ha hx hp hdiv (prime_divisor_of_fa_divides_fx_minus_x_h11 n f hn hpos hf a x p ha hx hp hdiv (prime_divisor_of_fa_divides_fx_minus_x_h10 n f hn hpos hf a x p ha hx hp hdiv (prime_divisor_of_fa_divides_fx_minus_x_h2 n f hn hpos hf a x p ha hx hp hdiv (prime_divisor_of_fa_divides_fx_minus_x_h1 n f hn hpos hf a x p ha hx hp hdiv))))

lemma f_n_is_power_of_two_for_even_n_h10 :
  ∀ (m : ℕ), m > 0 → (∀ p : ℕ, Nat.Prime p → p ∣ m → p = 2) → (∃ k : ℕ, m = 2 ^ k) := by
  intro m hm h
  exact ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hm.ne' fun hd hdm => h _ hd hdm⟩

lemma f_n_is_power_of_two_for_even_n_h1 (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (h_exists_k : ∃ k : ℤ, k > 1 ∧ f k ≠ k):
  ∀ (q : ℤ), Nat.Prime q.toNat → q ∣ f n → q = 2 := by
  intro q hq_prime hq_dvd; by_contra hq
  obtain ⟨k, hk1, hk2⟩ := h_exists_k
  have hq2 : q > 2 := by have := hq_prime.two_le; omega
  have h5 := prime_divisor_of_fa_divides_fx_minus_x n f hn hpos hf n q q hn (by omega) hq_prime hq_dvd
  rw [f_is_not_identity_implies_f_p_eq_1_for_p_gt_2 n f hn hpos hf ⟨k, by omega, hk2⟩ q hq_prime hq2] at h5
  have h6 : q ∣ 1 := by simpa using dvd_add h5 (dvd_refl q)
  have := Int.le_of_dvd one_pos h6; omega

lemma f_n_is_power_of_two_for_even_n_main (n : ℤ)
  (f : ℤ → ℤ)
  (hn : n > 0)
  (hpos : ∀ k : ℤ, k > 0 → f k > 0)
  (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat)
  (h_exists_k : ∃ k : ℤ, k > 1 ∧ f k ≠ k):
  ∃ k : ℕ, f n = 2 ^ k := by
  have h1 := f_n_is_power_of_two_for_even_n_h1 n f hn hpos hf h_exists_k
  have hp := hpos n hn
  obtain ⟨k, hk⟩ := f_n_is_power_of_two_for_even_n_h10 (f n).toNat (by omega) fun p hp' hd => by exact_mod_cast h1 p (by simpa using hp') (by rw [← Int.toNat_of_nonneg hp.le]; exact_mod_cast hd)
  exact ⟨k, by rw [← Int.toNat_of_nonneg hp.le, hk]; norm_cast⟩

theorem f_n_is_power_of_two_for_even_n (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) (h_exists_k : ∃ k : ℤ, k > 1 ∧ f k ≠ k) :
  ∃ k : ℕ, f n = 2 ^ k := by
  exact f_n_is_power_of_two_for_even_n_main n f hn hpos hf h_exists_k

lemma round1_h_main' (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) : f n ≤ 4 * n := by
  rcases imo2025_p3_subproblem_f1_is_1_or_f_is_const_1 f hpos hf with h1 | h1
  · linarith [h1 n hn]
  by_cases h2 : ∀ k : ℤ, k > 0 → f k = k
  · exact round1_h_subcase1 n f hn hpos hf h2
  push_neg at h2; obtain ⟨k, hk, hne⟩ := h2; have h5 : k ≠ 1 := fun h => hne (by rw [h]; exact h1)
  have h9 : f 3 = 1 := (f_is_not_identity_implies_f_p_eq_1_for_p_gt_2 n f hn hpos hf ⟨k, by omega, hne⟩) 3 (by decide) (by norm_num); have h10 := hf n 3 hn (by norm_num); rw [h9, one_pow] at h10
  obtain ⟨j, hj⟩ := f_n_is_power_of_two_for_even_n n f hn hpos hf ⟨k, by omega, hne⟩; have h14 := round1_h_k_le_padic n f j hn hpos hf (by rw [← hj]; exact h10); rw [lte_2_3n_minus_1 n hn] at h14
  exact round1_h6' n f hn hpos hf j hj (by split_ifs at h14 <;> omega)

theorem imo2025_p3_left (n : ℤ) (f : ℤ → ℤ) (hn : n > 0) (hpos : ∀ k : ℤ, k > 0 → f k > 0) (hf : ∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) : f n ≤ 4 * n := by
  exact round1_h_main' n f hn hpos hf

theorem imo2025_p3_right : ∃ (n : ℤ) (f : ℤ → ℤ), (n > 0) ∧ (∀ k : ℤ, k > 0 → f k > 0) ∧ (∀ a b : ℤ, a > 0 → b > 0 → f a ∣ b ^ a.toNat - (f b) ^ (f a).toNat) ∧ (f n ≥ 4 * n) := by
  obtain ⟨f, hf⟩ : ∃ f : ℤ → ℤ, ∀ k, f k = if k = 4 then 16 else if k % 2 = 1 then 1 else 2 := ⟨_, fun k => rfl⟩
  have hfour : f 4 = 16 := by simp [hf]
  have hodd : ∀ k, k % 2 = 1 → f k = 1 := fun k hk => by rw [hf, if_neg (show k ≠ 4 by omega), if_pos hk]
  have heven : ∀ k, k % 2 = 0 → k ≠ 4 → f k = 2 := fun k hk h => by rw [hf, if_neg h, if_neg (show ¬ (k % 2 = 1) by omega)]
  refine ⟨4, f, by norm_num, fun k _ => (by rw [hf]; split_ifs <;> norm_num), ?_, by norm_num [hfour]⟩
  intro a b ha hb
  by_cases h4 : a = 4
  · subst h4; rw [hfour, show (4 : ℤ).toNat = 4 from rfl, show (16 : ℤ).toNat = 16 from rfl]
    rcases (by omega : b % 2 = 0 ∨ b % 2 = 1) with hb2 | hb2
    · by_cases hb4 : b = 4
      · subst hb4; norm_num [hfour]
      · obtain ⟨c, rfl⟩ : ∃ c, b = 2 * c := ⟨b / 2, by omega⟩
        rw [heven _ hb2 hb4]
        exact ⟨c ^ 4 - 2 ^ 12, by ring⟩
    · rw [hodd b hb2, one_pow]
      have hm : b ^ 4 % 16 = 1 := by rcases (by omega : b % 16 = 1 ∨ b % 16 = 3 ∨ b % 16 = 5 ∨ b % 16 = 7 ∨ b % 16 = 9 ∨ b % 16 = 11 ∨ b % 16 = 13 ∨ b % 16 = 15) with h | h | h | h | h | h | h | h <;> simp [pow_succ, Int.mul_emod, h]
      omega
  rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with ha2 | ha2
  · rw [heven a ha2 h4, show (2 : ℤ).toNat = 2 from rfl]
    rcases (by omega : b % 2 = 0 ∨ b % 2 = 1) with hb2 | hb2
    · exact dvd_sub (dvd_pow (show (2:ℤ) ∣ b by omega) (show a.toNat ≠ 0 by omega)) (dvd_pow (by rw [hf]; split_ifs <;> omega) two_ne_zero)
    · rw [hodd b hb2, one_pow]
      obtain ⟨k, hk⟩ : Odd (b ^ a.toNat) := Odd.pow (Int.odd_iff.mpr hb2)
      rw [hk]; omega
  · rw [hodd a ha2]; exact one_dvd _
end IMO2025.P3
