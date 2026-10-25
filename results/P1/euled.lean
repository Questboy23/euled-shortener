import Mathlib

set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat Classical Polynomial
namespace IMO2025.P1
theorem k2_impossible_for_n3 (n : ℕ) (k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ))
  (hn : n = 3) (hk : k = 2)
  (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x))
  (hk_sunny : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) :
  False := by
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := lines) (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)
  rw [hk_sunny, Finset.filter_congr (p := fun l : ℝ × ℝ => ¬ (l.1 ≠ 0 ∧ l.1 ≠ -1)) (q := fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) fun l _ => by simp only [ne_eq, not_and_or, not_not]] at hsplit
  have round1_case2 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 1 → False := fun h421 => by
    have h422 : verts.card = 0 := by omega
    have mem : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a + b ≤ 4 → ∃ l ∈ lines, l.1 * (a : ℝ) + l.2 = (b : ℝ) := fun a b h1 h2 h3 =>
      (hmain (a, b) ((hallpoints (a, b)).2 ⟨h1, h2, by show a + b ≤ n + 1; omega⟩)).resolve_right (by simp [Finset.card_eq_zero.mp h422])
    obtain ⟨p, hp, hp1⟩ := mem 1 1 (by norm_num) (by norm_num) (by norm_num); obtain ⟨q, hq, hq1⟩ := mem 1 2 (by norm_num) (by norm_num) (by norm_num); obtain ⟨r, hr, hr1⟩ := mem 1 3 (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨s1, hs1, e21⟩ := mem 2 1 (by norm_num) (by norm_num) (by norm_num); obtain ⟨s2, hs2, e22⟩ := mem 2 2 (by norm_num) (by norm_num) (by norm_num); obtain ⟨s3, hs3, e31⟩ := mem 3 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at hp1 hq1 hr1 e21 e22 e31
    have ⟨hpq, hpr, hqr⟩ : p ≠ q ∧ p ≠ r ∧ q ≠ r := by refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> linarith
    have heq : ({p, q, r} : Finset (ℝ × ℝ)) = lines := Finset.eq_of_subset_of_card_le (fun l hl => by simp only [Finset.mem_insert, Finset.mem_singleton] at hl; rcases hl with rfl | rfl | rfl <;> assumption) (by have := Finset.card_eq_three.mpr ⟨p, q, r, hpq, hpr, hqr, rfl⟩; omega)
    have hmem : ∀ l ∈ lines, l = p ∨ l = q ∨ l = r := fun l hl => by rw [← heq] at hl; simpa using hl
    have hk : ∀ x ∈ lines, ∀ y ∈ lines, x ≠ y → (x.1 = 0 ∨ x.1 = -1) → (y.1 = 0 ∨ y.1 = -1) → False := fun x hx y hy hxy h1 h2 => by have hlt : 1 < (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card := Finset.one_lt_card.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, h1⟩, y, Finset.mem_filter.mpr ⟨hy, h2⟩, hxy⟩; rw [h421] at hlt; omega
    have key0 : (p.1 = 0 ∨ p.1 = -1) ∨ (q.1 = 0 ∨ q.1 = -1) ∨ (r.1 = 0 ∨ r.1 = -1) := by obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h421; have ha' := Finset.mem_singleton_self a; rw [← ha] at ha'; obtain ⟨hal, hpa⟩ := Finset.mem_filter.mp ha'; rcases hmem a hal with rfl | rfl | rfl <;> tauto
    rcases hmem s1 hs1 with rfl | rfl | rfl <;> rcases hmem s2 hs2 with rfl | rfl | rfl <;> rcases hmem s3 hs3 with rfl | rfl | rfl <;> first | linarith | exact hk _ hp _ hq hpq (by first | (left; linarith) | (right; linarith)) (by first | (left; linarith) | (right; linarith)) | exact hk _ hp _ hr hpr (by first | (left; linarith) | (right; linarith)) (by first | (left; linarith) | (right; linarith)) | exact hk _ hq _ hr hqr (by first | (left; linarith) | (right; linarith)) (by first | (left; linarith) | (right; linarith)) | (rcases key0 with (h | h) | (h | h) | (h | h) <;> linarith)
  rcases (show (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 0 ∨ (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 1 by omega) with h0 | h1
  · have hs : ∀ l ∈ lines, l.1 ≠ 0 ∧ l.1 ≠ -1 := fun l hl => by simpa [not_or] using Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp h0) hl
    subst hn
    have hv : verts.card = 1 := by omega
    obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp (show lines.card = 2 by omega)
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hv
    have ha := hs a (by simp); have hb := hs b (by simp)
    have h11 := hmain (1, 1) ((hallpoints _).2 (by norm_num)); have h12 := hmain (1, 2) ((hallpoints _).2 (by norm_num)); have h13 := hmain (1, 3) ((hallpoints _).2 (by norm_num))
    have h21 := hmain (2, 1) ((hallpoints _).2 (by norm_num)); have h22 := hmain (2, 2) ((hallpoints _).2 (by norm_num)); have h31 := hmain (3, 1) ((hallpoints _).2 (by norm_num))
    norm_num [or_assoc] at h11 h12 h13 h21 h22 h31
    rcases h11 with h11 | h11 | h11 <;> rcases h12 with h12 | h12 | h12 <;> rcases h13 with h13 | h13 | h13 <;> rcases h21 with h21 | h21 | h21 <;> rcases h22 with h22 | h22 | h22 <;> rcases h31 with h31 | h31 | h31 <;> (first | linarith | exact ha.1 (by linarith) | exact ha.2 (by linarith) | exact hb.1 (by linarith) | exact hb.2 (by linarith))
  · exact round1_case2 h1

lemma round1_h1 (k : ℕ)
  (lines : Finset (ℝ × ℝ))
  (verts : Finset ℝ)
  (points : Finset (ℕ × ℕ))
  (hcard : lines.card + verts.card = 3)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ 3 + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k):
  k ≤ 3 := by
  subst hk
  exact (Finset.card_filter_le _ _).trans (by omega)

lemma round1_h2 (k : ℕ)
  (lines : Finset (ℝ × ℝ))
  (verts : Finset ℝ)
  (points : Finset (ℕ × ℕ))
  (hcard : lines.card + verts.card = 3)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ 3 + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k):
  k ≠ 2 := by
  intro h
  exact k2_impossible_for_n3 3 k verts lines points (by norm_num) h hcard hallpoints hmain hk

theorem imo2025_p1_prop_n_eq_3_k_eq_0_1_3 (k : ℕ) (lines : Finset (ℝ × ℝ)) (verts : Finset ℝ) (points : Finset (ℕ × ℕ)) (hcard : lines.card + verts.card = 3) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ 3 + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) :
  k = 0 ∨ k = 1 ∨ k = 3 := by
  have h1 := round1_h1 k lines verts points hcard hallpoints hmain hk; have h2 := round1_h2 k lines verts points hcard hallpoints hmain hk
  omega

theorem inductive_step_if_contains_horizontal_line (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (hn : n ≥ 4) (hcover : ∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 →
    (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x)) (h_has_horizontal : ∃ l ∈ lines, l.1 = 0 ∧ l.2 = 1) (h_ih : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3): k = 0 ∨ k = 1 ∨ k = 3 := by
  obtain ⟨h, hmem, h0, h1⟩ := h_has_horizontal; have inj : Function.Injective (fun l : ℝ × ℝ => (l.1, l.2 - 1)) := fun a b hab => by simp only [Prod.mk.injEq] at hab; exact Prod.ext hab.1 (by linarith [hab.2])
  refine h_ih k verts ((lines.erase h).image (fun l => (l.1, l.2 - 1))) ?_ ?_ ?_
  · rw [Finset.card_image_of_injective _ inj, Finset.card_erase_of_mem hmem]; have := Finset.card_pos.mpr ⟨h, hmem⟩; omega
  · rintro ⟨a, b⟩ ⟨ha, hb, hab⟩; rcases hcover (a, b + 1) ⟨ha, by dsimp only; omega, by dsimp only; omega⟩ with ⟨l, hl, hl2⟩ | ⟨x, hx, hx2⟩
    · rcases eq_or_ne l h with rfl | hlh
      · dsimp only at hl2; rw [h0, h1] at hl2; push_cast at hl2; linarith [(by exact_mod_cast hb : (1:ℝ) ≤ b)]
      · exact Or.inl ⟨(l.1, l.2 - 1), Finset.mem_image.mpr ⟨l, Finset.mem_erase.mpr ⟨hlh, hl⟩, rfl⟩, by dsimp only at hl2 ⊢; push_cast at hl2; linarith⟩
    · exact Or.inr ⟨x, hx, hx2⟩
  · rw [Finset.filter_image, Finset.card_image_of_injective _ inj, ← hk]; have hnot : h ∉ lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1) := (by simp [h0]); simp [Finset.filter_erase, hnot]

theorem inductive_step_if_contains_vertical_line (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (hn : n ≥ 4) (hcover : ∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 →
    (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x)) (h_has_vert : ∃ x ∈ verts, x = 1) (h_ih : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3): k = 0 ∨ k = 1 ∨ k = 3 := by
  obtain ⟨x, hx, rfl⟩ := h_has_vert; have hi : Function.Injective (fun l : ℝ × ℝ => (l.1, l.2 + l.1)) := fun ⟨a, b⟩ ⟨c, d⟩ h => by simp only [Prod.mk.injEq] at h ⊢; constructor <;> linarith [h.1, h.2]
  have hsum : ((verts.erase 1).image (· - 1)).card + (lines.image (fun l : ℝ × ℝ => (l.1, l.2 + l.1))).card = n - 1 := by have := Finset.card_pos.2 ⟨1, hx⟩; rw [Finset.card_image_of_injective _ sub_left_injective, Finset.card_erase_of_mem hx, Finset.card_image_of_injective _ hi]; omega
  refine h_ih k _ _ hsum (fun p ⟨hp1, hp2, _⟩ => ?_) (by rw [Finset.filter_image, Finset.card_image_of_injective _ hi]; simpa using hk)
  rcases hcover (p.1 + 1, p.2) ⟨by dsimp only; omega, hp2, by dsimp only; omega⟩ with ⟨l, hl, he⟩ | ⟨y, hy, he⟩
  exacts [Or.inl ⟨(l.1, l.2 + l.1), Finset.mem_image_of_mem _ hl, by push_cast at he ⊢; linear_combination he⟩, Or.inr ⟨y - 1, Finset.mem_image.2 ⟨y, Finset.mem_erase.2 ⟨fun h => by push_cast at he; linarith [(by exact_mod_cast hp1 : (1:ℝ) ≤ p.1)], hy⟩, rfl⟩, by push_cast at he; linarith⟩]

lemma inductive_step_if_contains_rainy_diagonal_line_refined_main_proof (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn1 : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (hcover : ∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 →
    (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x)) (h_has_rainy_diagonal : ∃ l ∈ lines, l.1 = -1 ∧ l.2 = (n : ℝ) + 1) (h_ih : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3): k = 0 ∨ k = 1 ∨ k = 3 := by
  obtain ⟨l, hl, hl1, hl2⟩ := h_has_rainy_diagonal
  refine h_ih k verts (lines.erase l) ?_ ?_ ?_
  · rw [Finset.card_erase_of_mem hl]; have := Finset.card_pos.mpr ⟨l, hl⟩; omega
  · rintro p ⟨h1, h2, h3⟩; exact (hcover p ⟨h1, h2, by omega⟩).imp (fun ⟨m, hm, hmp⟩ => ⟨m, Finset.mem_erase.mpr ⟨fun h => by rw [h, hl1, hl2] at hmp; have h4 : (p.1:ℝ) + p.2 ≤ n := (by exact_mod_cast h3); linarith, hm⟩, hmp⟩) id
  · rw [← hk, Finset.filter_erase, Finset.erase_eq_of_notMem]; simp [hl1]

theorem inductive_step_if_contains_rainy_diagonal_line_refined (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (hn : n ≥ 4) (hcover : ∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 →
    (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x)) (h_has_rainy_diagonal : ∃ l ∈ lines, l.1 = -1 ∧ l.2 = (n : ℝ) + 1) (h_ih : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3): k = 0 ∨ k = 1 ∨ k = 3 := by
  exact inductive_step_if_contains_rainy_diagonal_line_refined_main_proof n k verts lines points (by linarith) hcard hallpoints hmain hk hcover h_has_rainy_diagonal h_ih

lemma num_points_on_boundary_main (n : ℕ) (hpoints : Finset (ℕ × ℕ)) (hpoints_def : ∀ p, p ∈ hpoints ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) hpoints).card = 3 * n - (if n = 1 then 2 else if n = 2 then 3 else 3) := by
  have hS : Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) hpoints = ((Finset.Icc 1 n).image fun y => (1, y)) ∪ ((Finset.Icc 2 n).image fun x => (x, 1)) ∪ ((Finset.Icc 2 (n - 1)).image fun x => (x, n + 1 - x)) := by
    ext ⟨x, y⟩; simp only [Finset.mem_filter, hpoints_def, Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Prod.mk.injEq]; constructor <;> intro h <;> first | (by_cases hx : x = 1 <;> by_cases hy : y = 1 <;> first | exact Or.inl (Or.inl ⟨y, by omega⟩) | exact Or.inl (Or.inr ⟨x, by omega⟩) | exact Or.inr ⟨x, by omega⟩) | (rcases h with ((⟨a, h⟩ | ⟨a, h⟩) | ⟨a, h⟩) <;> omega)
  have hAB : Disjoint ((Finset.Icc 1 n).image fun y => (1, y)) ((Finset.Icc 2 n).image fun x => (x, 1)) := by simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_Icc, Prod.forall, Prod.mk.injEq]; rintro a b ⟨c, hc, h1, h2⟩ ⟨d, hd, h3, h4⟩; omega
  have hABC : Disjoint (((Finset.Icc 1 n).image fun y => (1, y)) ∪ ((Finset.Icc 2 n).image fun x => (x, 1))) ((Finset.Icc 2 (n - 1)).image fun x => (x, n + 1 - x)) := by simp only [Finset.disjoint_left, Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Prod.forall, Prod.mk.injEq]; rintro a b (⟨c, hc, h1, h2⟩ | ⟨c, hc, h1, h2⟩) ⟨d, hd, h3, h4⟩ <;> omega
  rw [hS, Finset.card_union_of_disjoint hABC, Finset.card_union_of_disjoint hAB, Finset.card_image_of_injective (f := fun y : ℕ => ((1 : ℕ), y)) _ (fun a b h => congrArg Prod.snd h), Finset.card_image_of_injective (f := fun x : ℕ => (x, (1 : ℕ))) _ (fun a b h => congrArg Prod.fst h), Finset.card_image_of_injective (f := fun x : ℕ => (x, n + 1 - x)) _ (fun a b h => congrArg Prod.fst h)]; simp only [Nat.card_Icc]; split_ifs <;> omega

theorem num_points_on_boundary (n : ℕ) (hpoints : Finset (ℕ × ℕ)) (hpoints_def : ∀ p, p ∈ hpoints ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n+1) hpoints).card = 3*n - (if n=1 then 2 else if n=2 then 3 else 3) := by
  rw [num_points_on_boundary_main]; simp_all

lemma non_sunny_lines_cover_at_most_2_points_on_boundary_h_final (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (l : ℝ × ℝ)
  (h_non_sunny : l.1 ≠ 0 ∧ l.1 ≠ -1)
  (h_main : ∀ (x y z : ℕ × ℕ), x ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → y ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → z ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → x = y ∨ x = z ∨ y = z):
  (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2 := by
  by_contra! h
  obtain ⟨x, hx, y, hy, z, hz, a, b, c⟩ := Finset.two_lt_card.1 h
  grind

lemma non_sunny_lines_cover_at_most_2_points_on_boundary_h_main (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (l : ℝ × ℝ)
  (h_non_sunny : l.1 ≠ 0 ∧ l.1 ≠ -1):
  ∀ (x y z : ℕ × ℕ), x ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → y ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → z ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → x = y ∨ x = z ∨ y = z := by
  have hd : ∀ P Q : ℕ × ℕ, l.1 * P.1 + l.2 = P.2 → l.1 * Q.1 + l.2 = Q.2 → P.1 = Q.1 → P = Q := fun P Q hP hQ h => Prod.ext h (by rw [show (P.1:ℝ) = Q.1 by exact_mod_cast h] at hP; exact_mod_cast (by linarith : (P.2:ℝ) = Q.2))
  have key : ∀ A M B : ℕ × ℕ, A ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → M ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → B ∈ (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) → A.1 < M.1 → M.1 < B.1 → False := by
    intro A M B hA hM hB h1 h2
    obtain ⟨hAp, -, hAl⟩ := Finset.mem_filter.mp hA; obtain ⟨hMp, hMb, hMl⟩ := Finset.mem_filter.mp hM; obtain ⟨hBp, -, hBl⟩ := Finset.mem_filter.mp hB
    obtain ⟨a1, a2, a3⟩ := (hallpoints A).mp hAp; obtain ⟨-, b2, b3⟩ := (hallpoints B).mp hBp
    obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ : (A.1:ℝ) < M.1 ∧ (M.1:ℝ) < B.1 ∧ (1:ℝ) ≤ A.1 ∧ (1:ℝ) ≤ A.2 ∧ (1:ℝ) ≤ B.2 ∧ (A.1:ℝ) + A.2 ≤ n + 1 ∧ (B.1:ℝ) + B.2 ≤ n + 1 := by exact_mod_cast (⟨h1, h2, a1, a2, b2, a3, b3⟩ : A.1 < M.1 ∧ M.1 < B.1 ∧ 1 ≤ A.1 ∧ 1 ≤ A.2 ∧ 1 ≤ B.2 ∧ A.1 + A.2 ≤ n + 1 ∧ B.1 + B.2 ≤ n + 1)
    rcases (by exact_mod_cast hMb : (M.1:ℝ) = 1 ∨ (M.2:ℝ) = 1 ∨ (M.1:ℝ) + M.2 = n + 1) with e | e | e <;> rcases lt_or_gt_of_ne h_non_sunny.1 with d | d <;> rcases lt_or_gt_of_ne (show l.1 + 1 ≠ 0 from fun t => h_non_sunny.2 (by linarith)) with s | s <;> nlinarith
  intro x y z hx hy hz; by_contra! h
  have k1 : x.1 ≠ y.1 := fun e => h.1 (hd x y (Finset.mem_filter.mp hx).2.2 (Finset.mem_filter.mp hy).2.2 e); have k2 : x.1 ≠ z.1 := fun e => h.2.1 (hd x z (Finset.mem_filter.mp hx).2.2 (Finset.mem_filter.mp hz).2.2 e); have k3 : y.1 ≠ z.1 := fun e => h.2.2 (hd y z (Finset.mem_filter.mp hy).2.2 (Finset.mem_filter.mp hz).2.2 e)
  grind

theorem non_sunny_lines_cover_at_most_2_points_on_boundary (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (l : ℝ × ℝ) (h_non_sunny : l.1 ≠ 0 ∧ l.1 ≠ -1) :
  (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧
    (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2 := by
  exact non_sunny_lines_cover_at_most_2_points_on_boundary_h_final n k verts lines points hn hcard hallpoints hmain hk l h_non_sunny (non_sunny_lines_cover_at_most_2_points_on_boundary_h_main n k verts lines points hn hcard hallpoints hmain hk l h_non_sunny)

lemma round1_case_l1_eq_0 (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n) (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (l : ℝ × ℝ) (h_non_boundary : ¬ (l.1 = 0 ∧ l.2 = 1) ∧ ¬ (l.1 = -1 ∧ l.2 = n + 1))
  (h10 : l.1 = 0) :
  (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2 := by
  by_contra! hc; obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.1 hc
  simp only [Finset.mem_filter, h10, zero_mul, zero_add, ne_eq, Prod.ext_iff] at ha hb hc' hab hac hbc
  have key : a.2 = b.2 ∧ a.2 = c.2 ∧ a.2 ≠ 1 := ⟨by exact_mod_cast ha.2.2.symm.trans hb.2.2, by exact_mod_cast ha.2.2.symm.trans hc'.2.2, fun h => h_non_boundary.1 ⟨h10, by simp [ha.2.2, h]⟩⟩
  omega

lemma round1_case_l1_eq_neg1 (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n) (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (l : ℝ × ℝ) (h_non_boundary : ¬ (l.1 = 0 ∧ l.2 = 1) ∧ ¬ (l.1 = -1 ∧ l.2 = n + 1))
  (h12 : l.1 = -1) :
  (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2 := by
  rw [h12] at h_non_boundary ⊢
  refine (Finset.card_le_card (t := {(1, ⌊l.2⌋₊ - 1), (⌊l.2⌋₊ - 1, 1)}) ?_).trans Finset.card_le_two
  intro p hp; obtain ⟨-, hb, hl⟩ := Finset.mem_filter.1 hp
  have h2 : l.2 = ((p.1 + p.2 : ℕ) : ℝ) := by push_cast; linarith
  have h3 : p.1 + p.2 ≠ n + 1 := fun h => h_non_boundary.2 ⟨rfl, by rw [h2]; exact_mod_cast h⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, h2, Nat.floor_natCast]
  omega

theorem line_not_boundary_covers_at_most_2_boundary_points (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (l : ℝ × ℝ) (h_non_boundary : ¬ (l.1 = 0 ∧ l.2 = 1) ∧ ¬ (l.1 = -1 ∧ l.2 = n + 1)) :
  (Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧
    (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2 := by
  exact (by tauto : (l.1 ≠ 0 ∧ l.1 ≠ -1) ∨ l.1 = 0 ∨ l.1 = -1).elim (non_sunny_lines_cover_at_most_2_points_on_boundary n k verts lines points hn hcard hallpoints hmain hk l) fun h => h.elim (round1_case_l1_eq_0 n k verts lines points hn hcard hallpoints hmain hk l h_non_boundary) (round1_case_l1_eq_neg1 n k verts lines points hn hcard hallpoints hmain hk l h_non_boundary)

lemma vert_line_covers_at_most_two_boundary_points (n : ℕ)
  (points : Finset (ℕ × ℕ))
  (x : ℝ)
  (hx_neq1 : x ≠ 1):
  (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points).card ≤ 2 := by
  refine le_trans (Finset.card_le_card (t := {(⌊x⌋₊, 1), (⌊x⌋₊, n + 1 - ⌊x⌋₊)}) fun q hq => ?_) Finset.card_le_two
  obtain ⟨-, -, -, -, hd, rfl⟩ := Finset.mem_filter.mp hq; simp_all [Prod.ext_iff]; omega

lemma total_boundary_points_covered_by_at_most_2n_h1 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (h_not_y1 : ∀ l ∈ lines, ¬(l.1 = 0 ∧ l.2 = 1))
  (h_not_xn1 : ∀ l ∈ lines, ¬(l.1 = -1 ∧ l.2 = n + 1)):
  ∀ l ∈ lines, ¬ (l.1 = 0 ∧ l.2 = 1) ∧ ¬ (l.1 = -1 ∧ l.2 = n + 1) := by
  grind

lemma total_boundary_points_covered_by_at_most_2n_h2 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (h_not_v1 : 1 ∉ verts)
  (h_not_y1 : ∀ l ∈ lines, ¬(l.1 = 0 ∧ l.2 = 1))
  (h_not_xn1 : ∀ l ∈ lines, ¬(l.1 = -1 ∧ l.2 = n + 1))
  (h1 : ∀ l ∈ lines, ¬ (l.1 = 0 ∧ l.2 = 1) ∧ ¬ (l.1 = -1 ∧ l.2 = n + 1)):
  ∀ l ∈ lines, (Finset.filter (fun p => (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2 := by
  intro l hl
  exact line_not_boundary_covers_at_most_2_boundary_points n k verts lines points hn hcard hallpoints hmain hk l (h1 l hl)

lemma total_boundary_points_covered_by_at_most_2n_h3 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (h_not_v1 : 1 ∉ verts):
  ∀ x ∈ verts, x ≠ 1 := by
  grind

lemma total_boundary_points_covered_by_at_most_2n_h4 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (h_not_v1 : 1 ∉ verts)
  (h3 : ∀ x ∈ verts, x ≠ 1):
  ∀ x ∈ verts, (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points).card ≤ 2 := by
  intro x hx
  exact vert_line_covers_at_most_two_boundary_points n points x (h3 x hx)

lemma total_boundary_points_covered_by_at_most_2n_h_main (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : 3 ≤ n)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k)
  (h_not_v1 : 1 ∉ verts)
  (h_not_y1 : ∀ l ∈ lines, ¬(l.1 = 0 ∧ l.2 = 1))
  (h_not_xn1 : ∀ l ∈ lines, ¬(l.1 = -1 ∧ l.2 = n + 1))
  (h2 : ∀ l ∈ lines, (Finset.filter (fun p => (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points).card ≤ 2)
  (h4 : ∀ x ∈ verts, (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points).card ≤ 2):
  (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) points).card ≤ 2 * n := by
  refine (Finset.card_le_card (t := lines.biUnion (fun l => Finset.filter (fun p : ℕ × ℕ => (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) ∪ verts.biUnion (fun x => Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points)) ?_).trans ((Finset.card_union_le _ _).trans ?_)
  · intro p hp
    obtain ⟨hpts, hBd⟩ := Finset.mem_filter.1 hp
    have hb := (hallpoints p).1 hpts
    rcases hmain p hpts with ⟨l, hl, hon⟩ | ⟨x, hx, hpx⟩
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨l, hl, Finset.mem_filter.2 ⟨hpts, hBd, hon⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_filter.2 ⟨hpts, hb.1, hb.2.1, hb.2.2, hBd, hpx⟩⟩)
  · have := Finset.card_biUnion_le_card_mul lines _ 2 h2
    have := Finset.card_biUnion_le_card_mul verts _ 2 h4
    omega

theorem total_boundary_points_covered_by_at_most_2n (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (h_not_v1 : 1 ∉ verts) (h_not_y1 : ∀ l ∈ lines, ¬(l.1 = 0 ∧ l.2 = 1)) (h_not_xn1 : ∀ l ∈ lines, ¬(l.1 = -1 ∧ l.2 = n + 1)) : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n+1) points).card ≤ 2 * n := by
  exact total_boundary_points_covered_by_at_most_2n_h_main n k verts lines points hn hcard hallpoints hmain hk h_not_v1 h_not_y1 h_not_xn1 (total_boundary_points_covered_by_at_most_2n_h2 n k verts lines points hn hcard hallpoints hmain hk h_not_v1 h_not_y1 h_not_xn1 (total_boundary_points_covered_by_at_most_2n_h1 n k verts lines points h_not_y1 h_not_xn1)) (total_boundary_points_covered_by_at_most_2n_h4 n k verts lines points hn hcard hallpoints hmain hk h_not_v1 (total_boundary_points_covered_by_at_most_2n_h3 n k verts lines points h_not_v1))

lemma boundary_line_exists_at_any_cover_simplified_h_main (n : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : 4 ≤ n)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)):
  (∃ x ∈ verts, x = 1) ∨ (∃ l ∈ lines, (l.1 = 0 ∧ l.2 = 1) ∨ (l.1 = -1 ∧ l.2 = n + 1)) := by
  by_contra h
  have hb : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) points).card = 3 * n - 3 := by
    rw [num_points_on_boundary n points hallpoints]; split_ifs <;> omega
  have hc := total_boundary_points_covered_by_at_most_2n n _ verts lines points (by omega) hcard hallpoints hmain rfl
    (fun hx => h (Or.inl ⟨1, hx, rfl⟩))
    (fun l hl hl' => h (Or.inr ⟨l, hl, Or.inl hl'⟩))
    (fun l hl hl' => h (Or.inr ⟨l, hl, Or.inr hl'⟩))
  omega

theorem boundary_line_exists_at_any_cover_simplified (n : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ))
    (hn : 4 ≤ n)
    (hcard : lines.card + verts.card = n)
    (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
    (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)):
  (∃ x ∈ verts, x = 1) ∨ (∃ l ∈ lines, (l.1 = 0 ∧ l.2 = 1) ∨ (l.1 = -1 ∧ l.2 = n + 1)) := by
  apply boundary_line_exists_at_any_cover_simplified_h_main <;> assumption

lemma round1_main (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) : k = 0 ∨ k = 1 ∨ k = 3 := by
  revert k verts lines points; induction n using Nat.strong_induction_on with
  | h n ih => intro k verts lines points hcard hallpoints hmain hk; rcases eq_or_ne n 3 with rfl | h1; exact imo2025_p1_prop_n_eq_3_k_eq_0_1_3 k lines verts points hcard hallpoints hmain hk; have h4 := boundary_line_exists_at_any_cover_simplified n verts lines points (by omega) hcard hallpoints hmain; have hcover : ∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 → (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x) := fun p hp => (by simpa using hmain p ((hallpoints p).2 hp)); have h_ih : ∀ k' : ℕ, ∀ (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)), verts'.card + lines'.card = n - 1 → (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n → (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) → (lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k' → k' = 0 ∨ k' = 1 ∨ k' = 3 := fun k' verts' lines' h13 h14 h15 => ih (n - 1) (by omega) (by omega) k' verts' lines' ((Finset.Ico 1 (n + 1) ×ˢ Finset.Ico 1 (n + 1)).filter (fun p => p.1 + p.2 ≤ n)) (by omega) (fun p => (by simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico]; omega)) (fun p hp => h14 p (by simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hp; omega)) h15; rcases h4 with h41 | ⟨l, hl, h42 | h42⟩; exacts [inductive_step_if_contains_vertical_line n k verts lines points hcard hallpoints hmain hk (by omega) hcover h41 h_ih, inductive_step_if_contains_horizontal_line n k verts lines points hcard hallpoints hmain hk (by omega) hcover ⟨l, hl, h42⟩ h_ih, inductive_step_if_contains_rainy_diagonal_line_refined n k verts lines points (by omega) hcard hallpoints hmain hk (by omega) hcover ⟨l, hl, h42⟩ h_ih]

theorem imo2025_p1_left (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) : k = 0 ∨ k = 1 ∨ k = 3 := by
  exact round1_main n k verts lines points hn hcard hallpoints hmain hk

theorem imo2025_p1_right (n k : ℕ) (hn : 3 ≤ n) (hk : k = 0 ∨ k = 1 ∨ k = 3) : ∃ lines : Finset (ℝ × ℝ), ∃ xs : Finset ℝ, lines.card + xs.card = n ∧ (∀ a b : ℕ, a > 0 → b > 0 → a + b ≤ n + 1 → (∃ l ∈ lines, l.1 * a + l.2 = b) ∨ (∃ x ∈ xs, a = x)) ∧ (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k := by
  have hI : ∀ m : ℕ, ((Finset.Icc 1 m).image (Nat.cast : ℕ → ℝ)).card = m := fun m => by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Nat.card_Icc]; omega
  have hM : ∀ a m : ℕ, 0 < a → a ≤ m → ∃ x ∈ (Finset.Icc 1 m).image (Nat.cast : ℕ → ℝ), (a:ℝ) = x :=
    fun a m ha h => ⟨a, Finset.mem_image_of_mem _ (Finset.mem_Icc.2 ⟨by omega, h⟩), rfl⟩
  obtain rfl | rfl | rfl := hk
  · exact ⟨∅, (Finset.Icc 1 n).image (Nat.cast : ℕ → ℝ), by simp [hI], fun a b ha _ hab => Or.inr (hM a n ha (by omega)), by simp⟩
  · refine ⟨{(1, 1 - (n:ℝ))}, (Finset.Icc 1 (n-1)).image (Nat.cast : ℕ → ℝ), by rw [Finset.card_singleton, hI]; omega, fun a b ha hb hab => ?_, by norm_num [Finset.filter_singleton]⟩
    by_cases h : a ≤ n - 1
    · exact Or.inr (hM a _ ha h)
    · exact Or.inl ⟨_, Finset.mem_singleton_self _, (by obtain rfl : a = n := (by omega); obtain rfl : b = 1 := (by omega); norm_num)⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h3 : ({(-2, 2 * (m:ℝ) + 5), (1, -(m:ℝ)), (-1/2, (m:ℝ)/2 + 5/2)} : Finset (ℝ × ℝ)).card = 3 :=
      Finset.card_eq_three.2 ⟨_, _, _, by norm_num, by norm_num, by norm_num, rfl⟩
    refine ⟨{(-2, 2 * (m:ℝ) + 5), (1, -(m:ℝ)), (-1/2, (m:ℝ)/2 + 5/2)}, (Finset.Icc 1 m).image (Nat.cast : ℕ → ℝ), by rw [h3, hI]; omega, fun a b ha hb hab => ?_, by rw [Finset.filter_true_of_mem, h3]; simp only [Finset.mem_insert, Finset.mem_singleton]; rintro x (rfl | rfl | rfl) <;> norm_num⟩
    by_cases h : a ≤ m
    · exact Or.inr (hM a m ha h)
    · left
      have hb3 : b ≤ 3 := by omega
      have ha3 : a = m + 1 ∨ a = m + 2 ∨ a = m + 3 := by omega
      interval_cases b <;> rcases ha3 with rfl | rfl | rfl <;> first
        | exact ⟨(-2, 2 * (m:ℝ) + 5), by simp, by push_cast; linarith⟩
        | exact ⟨(1, -(m:ℝ)), by simp, by push_cast; linarith⟩
        | exact ⟨(-1/2, (m:ℝ)/2 + 5/2), by simp, by push_cast; linarith⟩
        | (exfalso; omega)
end IMO2025.P1
