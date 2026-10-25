import Mathlib

set_option pp.numericTypes true
set_option pp.funBinderTypes true
set_option maxHeartbeats 0
set_option maxRecDepth 1000
set_option tactic.hygienic false
open BigOperators Real Nat Topology Rat Classical Polynomial
namespace IMO2025.P1
lemma round1_case1 (n : ℕ)
  (k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : n = 3)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x))
  (h411 : ∀ l ∈ lines, l.1 ≠ 0 ∧ l.1 ≠ -1)
  (h412 : verts.card = 1):
  False := by
  subst hn
  obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp (show lines.card = 2 by omega)
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h412
  obtain ⟨ha1, ha2⟩ := h411 a (by simp)
  obtain ⟨hb1, hb2⟩ := h411 b (by simp)
  have h11 := hmain (1, 1) ((hallpoints _).2 (by norm_num))
  have h12 := hmain (1, 2) ((hallpoints _).2 (by norm_num))
  have h13 := hmain (1, 3) ((hallpoints _).2 (by norm_num))
  have h21 := hmain (2, 1) ((hallpoints _).2 (by norm_num))
  have h22 := hmain (2, 2) ((hallpoints _).2 (by norm_num))
  have h31 := hmain (3, 1) ((hallpoints _).2 (by norm_num))
  norm_num [Finset.mem_insert, Finset.mem_singleton, or_assoc] at h11 h12 h13 h21 h22 h31
  rcases h11 with h11 | h11 | h11 <;> rcases h12 with h12 | h12 | h12 <;> rcases h13 with h13 | h13 | h13 <;> rcases h21 with h21 | h21 | h21 <;> rcases h22 with h22 | h22 | h22 <;> rcases h31 with h31 | h31 | h31 <;> (first | linarith | exact ha1 (by linarith) | exact ha2 (by linarith) | exact hb1 (by linarith) | exact hb2 (by linarith))

lemma round1_case2 (n : ℕ)
  (k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (hn : n = 3)
  (hcard : lines.card + verts.card = n)
  (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x))
  (h421 : (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 1)
  (h422 : verts.card = 0):
  False := by
  have mem : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a + b ≤ 4 → ∃ l ∈ lines, l.1 * (a : ℝ) + l.2 = (b : ℝ) := by
    intro a b h1 h2 h3
    rcases hmain (a, b) ((hallpoints (a, b)).2 ⟨h1, h2, by show a + b ≤ n + 1; omega⟩) with h | ⟨x, hx, _⟩
    exacts [h, by simp [Finset.card_eq_zero.mp h422] at hx]
  obtain ⟨p, hp, hp1⟩ := mem 1 1 (by norm_num) (by norm_num) (by norm_num); obtain ⟨q, hq, hq1⟩ := mem 1 2 (by norm_num) (by norm_num) (by norm_num); obtain ⟨r, hr, hr1⟩ := mem 1 3 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨s1, hs1, e21⟩ := mem 2 1 (by norm_num) (by norm_num) (by norm_num); obtain ⟨s2, hs2, e22⟩ := mem 2 2 (by norm_num) (by norm_num) (by norm_num); obtain ⟨s3, hs3, e31⟩ := mem 3 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num at hp1 hq1 hr1 e21 e22 e31
  have ⟨hpq, hpr, hqr⟩ : p ≠ q ∧ p ≠ r ∧ q ≠ r := by refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> linarith
  have heq : ({p, q, r} : Finset (ℝ × ℝ)) = lines := Finset.eq_of_subset_of_card_le (fun l hl => by simp only [Finset.mem_insert, Finset.mem_singleton] at hl; rcases hl with rfl | rfl | rfl <;> assumption) (by have := Finset.card_eq_three.mpr ⟨p, q, r, hpq, hpr, hqr, rfl⟩; omega)
  have hmem : ∀ l ∈ lines, l = p ∨ l = q ∨ l = r := fun l hl => by rw [← heq] at hl; simpa using hl
  have hk : ∀ x ∈ lines, ∀ y ∈ lines, x ≠ y → (x.1 = 0 ∨ x.1 = -1) → (y.1 = 0 ∨ y.1 = -1) → False := fun x hx y hy hxy h1 h2 => by have hlt : 1 < (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card := Finset.one_lt_card.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, h1⟩, y, Finset.mem_filter.mpr ⟨hy, h2⟩, hxy⟩; rw [h421] at hlt; omega
  have key0 : (p.1 = 0 ∨ p.1 = -1) ∨ (q.1 = 0 ∨ q.1 = -1) ∨ (r.1 = 0 ∨ r.1 = -1) := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h421
    obtain ⟨hal, hpa⟩ := Finset.mem_filter.mp (show a ∈ lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) by rw [ha]; exact Finset.mem_singleton_self a)
    rcases hmem a hal with rfl | rfl | rfl <;> first | exact Or.inl hpa | exact Or.inr (Or.inl hpa) | exact Or.inr (Or.inr hpa)
  rcases hmem s1 hs1 with rfl | rfl | rfl <;> rcases hmem s2 hs2 with rfl | rfl | rfl <;> rcases hmem s3 hs3 with rfl | rfl | rfl <;> first | linarith | exact hk _ hp _ hq hpq (by first | (left; linarith) | (right; linarith)) (by first | (left; linarith) | (right; linarith)) | exact hk _ hp _ hr hpr (by first | (left; linarith) | (right; linarith)) (by first | (left; linarith) | (right; linarith)) | exact hk _ hq _ hr hqr (by first | (left; linarith) | (right; linarith)) (by first | (left; linarith) | (right; linarith)) | (rcases key0 with (h | h) | (h | h) | (h | h) <;> linarith)

theorem k2_impossible_for_n3 (n : ℕ) (k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ))
  (hn : n = 3) (hk : k = 2)
  (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1)
  (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x))
  (hk_sunny : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) :
  False := by
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card (s := lines) (fun l : ℝ × ℝ => l.1 ≠ 0 ∧ l.1 ≠ -1)
  have hneg : lines.filter (fun l : ℝ × ℝ => ¬ (l.1 ≠ 0 ∧ l.1 ≠ -1)) = lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1) := Finset.filter_congr fun l _ => by simp only [ne_eq, not_and_or, not_not]
  rw [hneg, hk_sunny] at hsplit
  rcases (show (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 0 ∨ (lines.filter (fun l : ℝ × ℝ => l.1 = 0 ∨ l.1 = -1)).card = 1 by omega) with h0 | h1
  · exact round1_case1 n k verts lines points hn hcard hallpoints hmain (fun l hl => by simpa [not_or] using Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp h0) hl) (by omega)
  · exact round1_case2 n k verts lines points hn hcard hallpoints hmain h1 (by omega)

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

lemma translation_equivalence_y_axis_h_main (n k_local : ℕ)
  (hn : n > 3)
  (H : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (h1 : verts.card + lines.card = n - 1)
  (h2 : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 2 ∧ p.1 + p.2 ≤ n + 1)
  (h3 : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x))
  (h4 : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k_local):
  k_local = 0 ∨ k_local = 1 ∨ k_local = 3 := by
  have hinj : Function.Injective (fun l : ℝ × ℝ => (l.1, l.2 - 1)) := fun a b h => by simpa [Prod.ext_iff] using h
  refine H k_local verts _ (by rwa [Finset.card_image_of_injective _ hinj]) (fun p hp => ?_) (by rw [Finset.filter_image, Finset.card_image_of_injective _ hinj]; exact h4)
  obtain ⟨hp1, hp2, hp3⟩ := hp
  rcases h3 (p.1, p.2 + 1) ((h2 _).2 ⟨hp1, by dsimp only; omega, by dsimp only; omega⟩) with ⟨l, hl, hl'⟩ | ⟨x, hx, hx'⟩
  · exact Or.inl ⟨(l.1, l.2 - 1), Finset.mem_image_of_mem _ hl, by push_cast at hl' ⊢; linarith⟩
  · exact Or.inr ⟨x, hx, hx'⟩

theorem inductive_step_if_contains_horizontal_line (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (hn : n ≥ 4) (hcover : ∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 →
    (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x)) (h_has_horizontal : ∃ l ∈ lines, l.1 = 0 ∧ l.2 = 1) (h_ih : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3): k = 0 ∨ k = 1 ∨ k = 3 := by
  obtain ⟨l₀, hl₀, hl₀1, hl₀2⟩ := h_has_horizontal
  have hpos := Finset.card_pos.mpr ⟨l₀, hl₀⟩
  let f : ℝ × ℝ → ℝ × ℝ := fun l => (l.1, l.2 - 1)
  have hf : Function.Injective f := fun a b h => by
    simp only [f, Prod.mk.injEq] at h; exact Prod.ext h.1 (by linarith [h.2])
  have hcov : ∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ (lines.erase l₀).image f, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x) := by
    rintro p ⟨h1, h2, h3⟩
    have hr : (1 : ℝ) ≤ p.2 := mod_cast h2
    rcases hcover (p.1, p.2 + 1) ⟨h1, (by dsimp only; omega), (by dsimp only; omega)⟩ with ⟨l, hl, he⟩ | ⟨x, hx, he⟩
    · push_cast at he
      have hne : l ≠ l₀ := by rintro rfl; rw [hl₀1, hl₀2] at he; linarith
      exact Or.inl ⟨f l, Finset.mem_image_of_mem f (Finset.mem_erase.mpr ⟨hne, hl⟩), by simp only [f]; linarith⟩
    · exact Or.inr ⟨x, hx, he⟩
  have hcard' : verts.card + ((lines.erase l₀).image f).card = n - 1 := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_erase_of_mem hl₀]; omega
  have hk' : (((lines.erase l₀).image f).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k := by
    rw [← hk, ← Finset.card_image_of_injective (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)) hf]
    congr 1; ext q; simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_erase]; constructor
    · rintro ⟨⟨a, ⟨_, ha⟩, rfl⟩, hq⟩; exact ⟨a, ⟨ha, hq⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hq⟩, rfl⟩; exact ⟨⟨a, ⟨fun h => hq.1 (by rw [h]; exact hl₀1), ha⟩, rfl⟩, hq⟩
  exact h_ih k verts _ hcard' hcov hk'

theorem inductive_step_if_contains_vertical_line (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (hn : n ≥ 4) (hcover : ∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 →
    (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x)) (h_has_vert : ∃ x ∈ verts, x = 1) (h_ih : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)),
    (verts'.card + lines'.card = n - 1) →
    (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n →
      (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) →
    ((lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k') →
    k' = 0 ∨ k' = 1 ∨ k' = 3): k = 0 ∨ k = 1 ∨ k = 3 := by
  obtain ⟨x, hx, rfl⟩ := h_has_vert
  have hi : Function.Injective (fun l : ℝ × ℝ => (l.1, l.2 + l.1)) := fun ⟨a, b⟩ ⟨c, d⟩ h => by simp only [Prod.mk.injEq] at h ⊢; constructor <;> linarith [h.1, h.2]
  have hV : ((verts.erase 1).image (fun x : ℝ => x - 1)).card = verts.card - 1 := by rw [Finset.card_image_of_injective _ (show Function.Injective (fun x : ℝ => x - 1) from sub_left_injective), Finset.card_erase_of_mem hx]
  have hF : ((lines.image (fun l : ℝ × ℝ => (l.1, l.2 + l.1))).filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k := by rw [Finset.filter_image, Finset.card_image_of_injective _ hi]; simpa using hk
  have hsum : ((verts.erase 1).image (fun x : ℝ => x - 1)).card + (lines.image (fun l : ℝ × ℝ => (l.1, l.2 + l.1))).card = n - 1 := by have := Finset.card_pos.2 ⟨1, hx⟩; rw [hV, Finset.card_image_of_injective _ hi]; omega
  refine h_ih k _ _ hsum (fun p ⟨hp1, hp2, hp3⟩ => ?_) hF
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
  · rintro p ⟨h1, h2, h3⟩
    rcases hcover p ⟨h1, h2, by omega⟩ with ⟨m, hm, hmp⟩ | h
    · refine Or.inl ⟨m, Finset.mem_erase.mpr ⟨?_, hm⟩, hmp⟩; rintro rfl; rw [hl1, hl2] at hmp
      have : p.1 + p.2 = n + 1 := by exact_mod_cast (show (p.1 : ℝ) + p.2 = n + 1 by linarith)
      omega
    · exact Or.inr h
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
    ext ⟨x, y⟩; simp only [Finset.mem_filter, hpoints_def, Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Prod.mk.injEq]; constructor
    · intro h; by_cases hx : x = 1 <;> by_cases hy : y = 1 <;> first | exact Or.inl (Or.inl ⟨y, by omega⟩) | exact Or.inl (Or.inr ⟨x, by omega⟩) | exact Or.inr ⟨x, by omega⟩
    · rintro ((⟨a, h⟩ | ⟨a, h⟩) | ⟨a, h⟩) <;> omega
  have hAB : Disjoint ((Finset.Icc 1 n).image fun y => (1, y)) ((Finset.Icc 2 n).image fun x => (x, 1)) := by simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_Icc, Prod.forall, Prod.mk.injEq]; rintro a b ⟨c, hc, h1, h2⟩ ⟨d, hd, h3, h4⟩; omega
  have hABC : Disjoint (((Finset.Icc 1 n).image fun y => (1, y)) ∪ ((Finset.Icc 2 n).image fun x => (x, 1))) ((Finset.Icc 2 (n - 1)).image fun x => (x, n + 1 - x)) := by simp only [Finset.disjoint_left, Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Prod.forall, Prod.mk.injEq]; rintro a b (⟨c, hc, h1, h2⟩ | ⟨c, hc, h1, h2⟩) ⟨d, hd, h3, h4⟩ <;> omega
  have i1 : Function.Injective fun y : ℕ => ((1 : ℕ), y) := fun a b h => congrArg Prod.snd h
  have i2 : Function.Injective fun x : ℕ => (x, (1 : ℕ)) := fun a b h => congrArg Prod.fst h
  have i3 : Function.Injective fun x : ℕ => (x, n + 1 - x) := fun a b h => congrArg Prod.fst h
  rw [hS, Finset.card_union_of_disjoint hABC, Finset.card_union_of_disjoint hAB, Finset.card_image_of_injective _ i1, Finset.card_image_of_injective _ i2, Finset.card_image_of_injective _ i3]; simp only [Nat.card_Icc]; split_ifs <;> omega

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
  by_contra h
  obtain ⟨x, hx, y, hy, z, hz, a, b, c⟩ := Finset.two_lt_card.1 (not_le.mp h)
  rcases h_main x y z hx hy hz with h1 | h1 | h1 <;> contradiction

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
  have key : ∀ A M B : ℕ × ℕ, A ∈ Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points → M ∈ Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points → B ∈ Finset.filter (fun p ↦ (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points → A.1 < M.1 → M.1 < B.1 → False := by
    intro A M B hA hM hB h1 h2
    obtain ⟨hAp, -, hAl⟩ := Finset.mem_filter.mp hA; obtain ⟨hMp, hMb, hMl⟩ := Finset.mem_filter.mp hM; obtain ⟨hBp, -, hBl⟩ := Finset.mem_filter.mp hB
    obtain ⟨a1, a2, a3⟩ := (hallpoints A).mp hAp; obtain ⟨b1, b2, b3⟩ := (hallpoints B).mp hBp
    have H : (M.1:ℝ) = 1 ∨ (M.2:ℝ) = 1 ∨ (M.1:ℝ) + M.2 = n + 1 := by exact_mod_cast hMb
    obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ : (A.1:ℝ) < M.1 ∧ (M.1:ℝ) < B.1 ∧ (A.1:ℝ) + A.2 ≤ n + 1 ∧ (B.1:ℝ) + B.2 ≤ n + 1 ∧ (1:ℝ) ≤ A.1 ∧ (1:ℝ) ≤ A.2 ∧ (1:ℝ) ≤ B.2 := by exact_mod_cast (show A.1 < M.1 ∧ M.1 < B.1 ∧ A.1 + A.2 ≤ n + 1 ∧ B.1 + B.2 ≤ n + 1 ∧ 1 ≤ A.1 ∧ 1 ≤ A.2 ∧ 1 ≤ B.2 from ⟨h1, h2, a3, b3, a1, a2, b2⟩)
    rcases H with e | e | e <;> rcases lt_or_gt_of_ne h_non_sunny.1 with d | d <;> rcases lt_or_gt_of_ne (show l.1 + 1 ≠ 0 from fun t => h_non_sunny.2 (by linarith)) with s | s <;> nlinarith
  intro x y z hx hy hz
  by_contra hne; push_neg at hne; obtain ⟨hxy, hxz, hyz⟩ := hne
  have hdist : ∀ P Q : ℕ × ℕ, l.1 * P.1 + l.2 = P.2 → l.1 * Q.1 + l.2 = Q.2 → P.1 = Q.1 → P = Q := by
    intro P Q hP hQ h; refine Prod.ext h ?_; have h' : (P.1:ℝ) = Q.1 := (by exact_mod_cast h); have : (P.2:ℝ) = Q.2 := (by rw [← hP, ← hQ, h']); exact_mod_cast this
  have hxy' : x.1 ≠ y.1 := (fun h => hxy (hdist x y (Finset.mem_filter.mp hx).2.2 (Finset.mem_filter.mp hy).2.2 h)); have hxz' : x.1 ≠ z.1 := (fun h => hxz (hdist x z (Finset.mem_filter.mp hx).2.2 (Finset.mem_filter.mp hz).2.2 h)); have hyz' : y.1 ≠ z.1 := (fun h => hyz (hdist y z (Finset.mem_filter.mp hy).2.2 (Finset.mem_filter.mp hz).2.2 h))
  rcases lt_or_gt_of_ne hxy' with h1 | h1 <;> rcases lt_or_gt_of_ne hxz' with h2 | h2 <;> rcases lt_or_gt_of_ne hyz' with h3 | h3 <;> first | exact key x y z hx hy hz (by omega) (by omega) | exact key x z y hx hz hy (by omega) (by omega) | exact key y x z hy hx hz (by omega) (by omega) | exact key y z x hy hz hx (by omega) (by omega) | exact key z x y hz hx hy (by omega) (by omega) | exact key z y x hz hy hx (by omega) (by omega)

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
  by_contra! hc
  obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.1 hc
  simp only [Finset.mem_filter, h10, zero_mul, zero_add, ne_eq, Prod.ext_iff] at ha hb hc' hab hac hbc
  have e1 : a.2 = b.2 := by exact_mod_cast ha.2.2.symm.trans hb.2.2
  have e2 : a.2 = c.2 := by exact_mod_cast ha.2.2.symm.trans hc'.2.2
  have f1 : a.2 ≠ 1 := fun h => h_non_boundary.1 ⟨h10, by simp [ha.2.2, h]⟩
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
  exact (show (l.1 ≠ 0 ∧ l.1 ≠ -1) ∨ l.1 = 0 ∨ l.1 = -1 from by tauto).elim (non_sunny_lines_cover_at_most_2_points_on_boundary n k verts lines points hn hcard hallpoints hmain hk l) (fun h => h.elim (round1_case_l1_eq_0 n k verts lines points hn hcard hallpoints hmain hk l h_non_boundary) (round1_case_l1_eq_neg1 n k verts lines points hn hcard hallpoints hmain hk l h_non_boundary))

lemma vert_line_covers_at_most_two_boundary_points (n : ℕ)
  (points : Finset (ℕ × ℕ))
  (x : ℝ)
  (hx_neq1 : x ≠ 1):
  (Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points).card ≤ 2 := by
  refine le_trans (Finset.card_le_card (t := {(⌊x⌋₊, 1), (⌊x⌋₊, n + 1 - ⌊x⌋₊)}) fun q hq => ?_) Finset.card_le_two
  obtain ⟨-, -, -, -, h4, h5⟩ := Finset.mem_filter.mp hq
  have hqa : q.1 = ⌊x⌋₊ := (by rw [← h5]; simp); have ha1 : q.1 ≠ 1 := fun h => hx_neq1 (by rw [← h5]; simp [h])
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]; omega

lemma total_boundary_points_covered_by_at_most_2n_h1 (n k : ℕ)
  (verts : Finset ℝ)
  (lines : Finset (ℝ × ℝ))
  (points : Finset (ℕ × ℕ))
  (h_not_y1 : ∀ l ∈ lines, ¬(l.1 = 0 ∧ l.2 = 1))
  (h_not_xn1 : ∀ l ∈ lines, ¬(l.1 = -1 ∧ l.2 = n + 1)):
  ∀ l ∈ lines, ¬ (l.1 = 0 ∧ l.2 = 1) ∧ ¬ (l.1 = -1 ∧ l.2 = n + 1) := by
  intro l hl
  exact ⟨h_not_y1 l hl, h_not_xn1 l hl⟩

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
  rintro x hx rfl
  exact h_not_v1 hx

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
  have hsub : Finset.filter (fun p : ℕ × ℕ => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) points ⊆
      lines.biUnion (fun l => Finset.filter (fun p : ℕ × ℕ => (p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1) ∧ (l.1 * p.1 + l.2 = p.2)) points) ∪
      verts.biUnion (fun x => Finset.filter (fun p : ℕ × ℕ => p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 ∧ ((p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n + 1)) ∧ (p.1 = x)) points) := by
    intro p hp
    have hb := (hallpoints p).1 (Finset.mem_filter.1 hp).1
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter] at hp ⊢
    obtain ⟨hpts, hBd⟩ := hp
    rcases hmain p hpts with ⟨l, hl, hon⟩ | ⟨x, hx, hpx⟩
    · exact Or.inl ⟨l, hl, hpts, hBd, hon⟩
    · exact Or.inr ⟨x, hx, hpts, hb.1, hb.2.1, hb.2.2, hBd, hpx⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  have hA := Finset.card_biUnion_le_card_mul lines _ 2 h2
  have hB := Finset.card_biUnion_le_card_mul verts _ 2 h4
  omega

theorem total_boundary_points_covered_by_at_most_2n (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) (h_not_v1 : 1 ∉ verts) (h_not_y1 : ∀ l ∈ lines, ¬(l.1 = 0 ∧ l.2 = 1)) (h_not_xn1 : ∀ l ∈ lines, ¬(l.1 = -1 ∧ l.2 = n + 1)) : (Finset.filter (fun p => p.1 = 1 ∨ p.2 = 1 ∨ p.1 + p.2 = n+1) points).card ≤ 2 * n := by exact total_boundary_points_covered_by_at_most_2n_h_main n k verts lines points hn hcard hallpoints hmain hk h_not_v1 h_not_y1 h_not_xn1 (total_boundary_points_covered_by_at_most_2n_h2 n k verts lines points hn hcard hallpoints hmain hk h_not_v1 h_not_y1 h_not_xn1 (total_boundary_points_covered_by_at_most_2n_h1 n k verts lines points h_not_y1 h_not_xn1)) (total_boundary_points_covered_by_at_most_2n_h4 n k verts lines points hn hcard hallpoints hmain hk h_not_v1 (total_boundary_points_covered_by_at_most_2n_h3 n k verts lines points h_not_v1))

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
  exact boundary_line_exists_at_any_cover_simplified_h_main n verts lines points hn hcard hallpoints hmain

lemma round1_main (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) : k = 0 ∨ k = 1 ∨ k = 3 := by
  have h : ∀ n : ℕ, 3 ≤ n → ∀ k : ℕ, ∀ (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)), lines.card + verts.card = n → (∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) → (∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) → (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k → k = 0 ∨ k = 1 ∨ k = 3 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn3 k verts lines points hcard hallpoints hmain hk
      by_cases h1 : n = 3
      · subst h1; exact imo2025_p1_prop_n_eq_3_k_eq_0_1_3 k lines verts points hcard hallpoints hmain hk
      have h2 : 4 ≤ n := by omega
      have h4 := boundary_line_exists_at_any_cover_simplified n verts lines points (by linarith) hcard hallpoints hmain
      have hcover : ∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1 → (∃ l ∈ lines, l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts, (p.1 : ℝ) = x) := fun p hp => by simpa using hmain p ((hallpoints p).2 hp)
      have h_ih : ∀ (k' : ℕ) (verts' : Finset ℝ) (lines' : Finset (ℝ × ℝ)), verts'.card + lines'.card = n - 1 → (∀ p : ℕ × ℕ, p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n → (∃ l ∈ lines', l.1 * (p.1 : ℝ) + l.2 = (p.2 : ℝ)) ∨ (∃ x ∈ verts', (p.1 : ℝ) = x)) → (lines'.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k' → k' = 0 ∨ k' = 1 ∨ k' = 3 := fun k' verts' lines' h13 h14 h15 => by
        refine ih (n - 1) (by omega) (by omega) k' verts' lines' ((Finset.Ico 1 (n + 1) ×ˢ Finset.Ico 1 (n + 1)).filter (fun p => p.1 + p.2 ≤ n)) (by omega) (fun p => ?_) (fun p hp => ?_) h15
        · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico]; omega
        · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ico] at hp; exact h14 p ⟨by omega, by omega, hp.2⟩
      rcases h4 with h41 | ⟨l, hl, h42 | h42⟩
      · exact inductive_step_if_contains_vertical_line n k verts lines points hcard hallpoints hmain hk (by linarith) hcover h41 h_ih
      · exact inductive_step_if_contains_horizontal_line n k verts lines points hcard hallpoints hmain hk (by linarith) hcover ⟨l, hl, h42⟩ h_ih
      · exact inductive_step_if_contains_rainy_diagonal_line_refined n k verts lines points (by linarith) hcard hallpoints hmain hk (by linarith) hcover ⟨l, hl, h42⟩ h_ih
  exact h n hn k verts lines points hcard hallpoints hmain hk

theorem imo2025_p1_left (n k : ℕ) (verts : Finset ℝ) (lines : Finset (ℝ × ℝ)) (points : Finset (ℕ × ℕ)) (hn : 3 ≤ n) (hcard : lines.card + verts.card = n) (hallpoints : ∀ p, p ∈ points ↔ p.1 ≥ 1 ∧ p.2 ≥ 1 ∧ p.1 + p.2 ≤ n + 1) (hmain : ∀ p ∈ points, (∃ l ∈ lines, l.1 * p.1 + l.2 = p.2) ∨ (∃ x ∈ verts, p.1 = x)) (hk : (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k) : k = 0 ∨ k = 1 ∨ k = 3 := by
  exact round1_main n k verts lines points hn hcard hallpoints hmain hk

theorem imo2025_p1_right (n k : ℕ) (hn : 3 ≤ n) (hk : k = 0 ∨ k = 1 ∨ k = 3) : ∃ lines : Finset (ℝ × ℝ), ∃ xs : Finset ℝ, lines.card + xs.card = n ∧ (∀ a b : ℕ, a > 0 → b > 0 → a + b ≤ n + 1 → (∃ l ∈ lines, l.1 * a + l.2 = b) ∨ (∃ x ∈ xs, a = x)) ∧ (lines.filter (fun l ↦ l.1 ≠ 0 ∧ l.1 ≠ -1)).card = k := by
  have hI : ∀ m : ℕ, ((Finset.Icc 1 m).image (Nat.cast : ℕ → ℝ)).card = m := fun m => by rw [Finset.card_image_of_injective _ Nat.cast_injective, Nat.card_Icc]; omega
  have hM : ∀ a m : ℕ, 0 < a → a ≤ m → ∃ x ∈ (Finset.Icc 1 m).image (Nat.cast : ℕ → ℝ), (a:ℝ) = x := fun a m ha h => ⟨a, Finset.mem_image.2 ⟨a, Finset.mem_Icc.2 ⟨by omega, h⟩, rfl⟩, rfl⟩
  rcases hk with rfl | rfl | rfl
  · refine ⟨∅, (Finset.Icc 1 n).image (Nat.cast : ℕ → ℝ), by simp [hI], fun a b ha _ hab => Or.inr (hM a n ha (by omega)), by simp⟩
  · refine ⟨{(1, 1 - (n:ℝ))}, (Finset.Icc 1 (n-1)).image (Nat.cast : ℕ → ℝ), by rw [Finset.card_singleton, hI]; omega, ?_, by norm_num [Finset.filter_singleton]⟩
    intro a b ha hb hab; by_cases h : a ≤ n - 1
    · exact Or.inr (hM a _ ha h)
    · have e : a = n := by omega
      have f : b = 1 := by omega
      subst f
      exact Or.inl ⟨(1, 1 - (n:ℝ)), Finset.mem_singleton_self _, by rw [e]; dsimp only; push_cast; ring⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h3 : ({(-2, 2 * (m:ℝ) + 5), (1, -(m:ℝ)), (-1/2, (m:ℝ)/2 + 5/2)} : Finset (ℝ × ℝ)).card = 3 := by rw [Finset.card_eq_three]; exact ⟨(-2, 2 * (m:ℝ) + 5), (1, -(m:ℝ)), (-1/2, (m:ℝ)/2 + 5/2), by norm_num, by norm_num, by norm_num, rfl⟩
    refine ⟨{(-2, 2 * (m:ℝ) + 5), (1, -(m:ℝ)), (-1/2, (m:ℝ)/2 + 5/2)}, (Finset.Icc 1 m).image (Nat.cast : ℕ → ℝ), by rw [h3, hI]; omega, ?_, ?_⟩
    · intro a b ha hb hab
      by_cases h : a ≤ m
      · exact Or.inr (hM a m ha h)
      · left
        have hb3 : b ≤ 3 := by omega
        have ha3 : a = m + 1 ∨ a = m + 2 ∨ a = m + 3 := by omega
        interval_cases b <;> rcases ha3 with rfl | rfl | rfl <;> first | exact ⟨(-2, 2 * (m:ℝ) + 5), by simp, by dsimp only; push_cast; linarith⟩ | exact ⟨(1, -(m:ℝ)), by simp, by dsimp only; push_cast; linarith⟩ | exact ⟨(-1/2, (m:ℝ)/2 + 5/2), by simp, by dsimp only; push_cast; linarith⟩ | (exfalso; omega)
    · rw [Finset.filter_true_of_mem, h3]; intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx; rcases hx with rfl | rfl | rfl <;> norm_num
end IMO2025.P1
