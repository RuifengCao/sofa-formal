/-
# Sofa/NicheBound.lean — the geometric input to Baek Thm 6.3.3

Thm 6.3.3 bounds the side length `σ_K(t)` of a maximum polygon cap by `k₀(g⁺_K(t))δ + O(δ²)`.
Its proof splits the niche side `X = {x : R(x) = b_t(x)} ∩ posR` into three pieces, each of which
is an intersection of two half-lines in the `x`-coordinate, hence an interval whose length is an
explicit expression in the support values.  This file builds that interval arithmetic.

The key observation (which replaces Baek's detour through `∂N_Θ(K)` and `Q⁻_K(u)`) is that in the
graph representation the containment `X \ R ⊆ S` is *immediate*: `roofR ≥ min(b_u, d_u)` for every
`u ∈ Θ`, so `R(x) = b_t(x) < d_u(x)` forces `b_u(x) ≤ b_t(x)`.

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.Injective
import Sofa.PolyBalance

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

/-! ## Comparing two lines as graphs over the `x`-axis -/

lemma lineFn_le_lineFn_iff {s₁ s₂ : ℝ} (h1 : 0 < sin s₁) (h2 : 0 < sin s₂) (c₁ c₂ x : ℝ) :
    lineFn s₁ c₁ x ≤ lineFn s₂ c₂ x ↔ x * sin (s₁ - s₂) ≤ sin s₁ * c₂ - sin s₂ * c₁ := by
  rw [lineFn, lineFn, div_le_div_iff₀ h1 h2, sin_sub]
  constructor <;> intro h <;> nlinarith [h]

/-- The comparison set is a left half-line when `sin (s₁ − s₂) > 0`. -/
lemma setOf_lineFn_le_pos {s₁ s₂ : ℝ} (h1 : 0 < sin s₁) (h2 : 0 < sin s₂)
    (hd : 0 < sin (s₁ - s₂)) (c₁ c₂ : ℝ) :
    {x : ℝ | lineFn s₁ c₁ x ≤ lineFn s₂ c₂ x}
      = Iic ((sin s₁ * c₂ - sin s₂ * c₁) / sin (s₁ - s₂)) := by
  ext x
  rw [mem_ofPred_eq, lineFn_le_lineFn_iff h1 h2, mem_Iic, le_div_iff₀ hd]

/-- The comparison set is a right half-line when `sin (s₁ − s₂) < 0`. -/
lemma setOf_lineFn_le_neg {s₁ s₂ : ℝ} (h1 : 0 < sin s₁) (h2 : 0 < sin s₂)
    (hd : sin (s₁ - s₂) < 0) (c₁ c₂ : ℝ) :
    {x : ℝ | lineFn s₁ c₁ x ≤ lineFn s₂ c₂ x}
      = Ici ((sin s₁ * c₂ - sin s₂ * c₁) / sin (s₁ - s₂)) := by
  ext x
  rw [mem_ofPred_eq, lineFn_le_lineFn_iff h1 h2, mem_Ici, div_le_iff_of_neg hd]

/-- The `x`-measure of a "two half-line" piece of the line with normal `s₁`. -/
lemma volume_le_of_subset_Icc {S : Set ℝ} {a b : ℝ} (hS : S ⊆ Icc a b) :
    volume S ≤ ENNReal.ofReal (b - a) := by
  refine le_trans (measure_mono hS) ?_
  rw [Real.volume_Icc]

lemma lineFn_eq_lineFn_iff {s₁ s₂ : ℝ} (h1 : 0 < sin s₁) (h2 : 0 < sin s₂) (c₁ c₂ x : ℝ) :
    lineFn s₁ c₁ x = lineFn s₂ c₂ x ↔ x * sin (s₁ - s₂) = sin s₁ * c₂ - sin s₂ * c₁ := by
  constructor
  · intro h
    have e1 := (lineFn_le_lineFn_iff h1 h2 c₁ c₂ x).1 h.le
    have e2 := (lineFn_le_lineFn_iff h2 h1 c₂ c₁ x).1 h.ge
    have : sin (s₂ - s₁) = -sin (s₁ - s₂) := by rw [← Real.sin_neg]; ring_nf
    rw [this] at e2
    linarith
  · intro h
    refine le_antisymm ((lineFn_le_lineFn_iff h1 h2 c₁ c₂ x).2 h.le) ?_
    refine (lineFn_le_lineFn_iff h2 h1 c₂ c₁ x).2 ?_
    have : sin (s₂ - s₁) = -sin (s₁ - s₂) := by rw [← Real.sin_neg]; ring_nf
    rw [this]
    linarith

lemma volume_setOf_lineFn_eq {s₁ s₂ : ℝ} (h1 : 0 < sin s₁) (h2 : 0 < sin s₂)
    (hd : sin (s₁ - s₂) ≠ 0) (c₁ c₂ : ℝ) :
    volume {x : ℝ | lineFn s₁ c₁ x = lineFn s₂ c₂ x} = 0 := by
  have he : {x : ℝ | lineFn s₁ c₁ x = lineFn s₂ c₂ x}
      = {(sin s₁ * c₂ - sin s₂ * c₁) / sin (s₁ - s₂)} := by
    ext x
    rw [mem_ofPred_eq, lineFn_eq_lineFn_iff h1 h2, mem_singleton_iff, eq_div_iff hd]
  rw [he]
  exact measure_singleton _

/-! ## The niche side and its three pieces -/

/-- The inner wall of the hallway with normal `s`, as a graph over the `x`-axis. -/
def wall (h : ℝ → ℝ) (s x : ℝ) : ℝ := lineFn s (h s - 1) x

lemma roofR_eq_wall (hΘ : Θ.Nonempty) (h : ℝ → ℝ) (x : ℝ) :
    roofR Θ hΘ h x = Θ.sup' hΘ fun s => min (wall h s x) (wall h (s + π / 2) x) := rfl

lemma min_wall_le_roofR (hΘ : Θ.Nonempty) (h : ℝ → ℝ) {s : ℝ} (hs : s ∈ Θ) (x : ℝ) :
    min (wall h s x) (wall h (s + π / 2) x) ≤ roofR Θ hΘ h x :=
  Finset.le_sup' (fun s => min (wall h s x) (wall h (s + π / 2) x)) hs

/-- The "crossing" set: where the niche roof meets the `t`-wall only by accident. -/
def crossSet (Θ : Finset ℝ) (h : ℝ → ℝ) (t : ℝ) : Set ℝ :=
  ⋃ s ∈ Θ.erase t,
    ({x : ℝ | wall h s x = wall h t x} ∪ {x : ℝ | wall h (s + π / 2) x = wall h t x})

/-- The piece of the `t`-wall above the inner wall `d_{t−δ}`. -/
def pieceL (h : ℝ → ℝ) (t δ : ℝ) : Set ℝ :=
  {x : ℝ | wall h t x ≤ wall h (t + π / 2) x ∧ wall h (t - δ + π / 2) x ≤ wall h t x}

/-- The piece of the `t`-wall above the inner wall `d_{t+δ}`. -/
def pieceR (h : ℝ → ℝ) (t δ : ℝ) : Set ℝ :=
  {x : ℝ | wall h t x ≤ wall h (t + π / 2) x ∧ wall h (t + δ + π / 2) x ≤ wall h t x}

/-- The piece of the `t`-wall above both neighbouring `b`-walls. -/
def pieceS (h : ℝ → ℝ) (t δ : ℝ) : Set ℝ :=
  {x : ℝ | wall h (t - δ) x ≤ wall h t x ∧ wall h (t + δ) x ≤ wall h t x}

/-- **The covering.**  In the graph representation this replaces Baek's argument through
`∂N_Θ(K)` and the quadrants `Q⁻_K(u)`. -/
theorem actR_subset_pieces {Θ : Finset ℝ} (hΘ : Θ.Nonempty) (h : ℝ → ℝ) {t δ : ℝ}
    (htm : t - δ ∈ Θ) (htp : t + δ ∈ Θ) :
    {x : ℝ | roofR Θ hΘ h x = wall h t x}
      ⊆ crossSet Θ h t ∪ pieceL h t δ ∪ pieceR h t δ ∪ pieceS h t δ := by
  intro x hx
  have hx' : roofR Θ hΘ h x = wall h t x := hx
  rcases le_or_gt (wall h t x) (wall h (t + π / 2) x) with hdt | hdt
  · -- the honest side of the wall
    rcases le_or_gt (wall h (t - δ + π / 2) x) (wall h t x) with h1 | h1
    · exact Or.inl (Or.inl (Or.inr ⟨hdt, h1⟩))
    rcases le_or_gt (wall h (t + δ + π / 2) x) (wall h t x) with h2 | h2
    · exact Or.inl (Or.inr ⟨hdt, h2⟩)
    refine Or.inr ⟨?_, ?_⟩
    · have hle := min_wall_le_roofR hΘ h htm x
      rw [hx'] at hle
      rcases min_cases (wall h (t - δ) x) (wall h (t - δ + π / 2) x) with ⟨he, -⟩ | ⟨he, -⟩
      · rw [he] at hle; exact hle
      · rw [he] at hle; exact absurd hle (not_le.2 h1)
    · have hle := min_wall_le_roofR hΘ h htp x
      rw [hx'] at hle
      rcases min_cases (wall h (t + δ) x) (wall h (t + δ + π / 2) x) with ⟨he, -⟩ | ⟨he, -⟩
      · rw [he] at hle; exact hle
      · rw [he] at hle; exact absurd hle (not_le.2 h2)
  · -- the accidental side: the maximum is attained at some `s ≠ t`
    obtain ⟨s, hs, hseq⟩ := Finset.exists_mem_eq_sup' hΘ
      (fun s => min (wall h s x) (wall h (s + π / 2) x))
    have hsup : roofR Θ hΘ h x = min (wall h s x) (wall h (s + π / 2) x) := hseq
    rw [hx'] at hsup
    have hst : s ≠ t := by
      intro heq
      rw [heq, min_eq_right hdt.le] at hsup
      exact hdt.ne hsup.symm
    have hmin : min (wall h s x) (wall h (s + π / 2) x) = wall h t x := hsup.symm
    refine Or.inl (Or.inl (Or.inl ?_))
    refine mem_biUnion (Finset.mem_erase.2 ⟨hst, hs⟩) ?_
    rcases min_cases (wall h s x) (wall h (s + π / 2) x) with ⟨he, -⟩ | ⟨he, -⟩
    · exact Or.inl (he.symm.trans hmin)
    · exact Or.inr (he.symm.trans hmin)

/-! ## The `crossSet` is null -/

private lemma sin_ne_zero_of_abs_lt {a : ℝ} (h0 : a ≠ 0) (h1 : -(π / 2) < a) (h2 : a < π / 2) :
    sin a ≠ 0 := by
  have hpi := pi_gt_three
  rcases lt_trichotomy a 0 with hneg | hzero | hpos
  · have : 0 < sin (-a) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [Real.sin_neg] at this
    linarith
  · exact absurd hzero h0
  · exact ne_of_gt (sin_pos_of_pos_of_lt_pi hpos (by linarith))

theorem volume_crossSet {Θ : Finset ℝ} (hrange : ∀ s ∈ Θ, 0 < s ∧ s < π / 2) (h : ℝ → ℝ)
    {t : ℝ} (ht : t ∈ Θ) : volume (crossSet Θ h t) = 0 := by
  have hpi := pi_gt_three
  obtain ⟨ht0, ht2⟩ := hrange t ht
  have htsin : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 (by linarith)
  refine (measure_biUnion_null_iff ((Θ.erase t).finite_toSet.countable)).2 fun s hs => ?_
  have hs' : s ∈ Θ := Finset.mem_of_mem_erase hs
  have hne : s ≠ t := Finset.ne_of_mem_erase hs
  obtain ⟨hs0, hs2⟩ := hrange s hs'
  have hssin : 0 < sin s := sin_pos_of_pos_of_lt_pi hs0 (by linarith)
  have hshalf : 0 < sin (s + π / 2) := by
    rw [Real.sin_add_pi_div_two]
    exact cos_pos_of_mem_Ioo ⟨by linarith, hs2⟩
  refine measure_union_null ?_ ?_
  · exact volume_setOf_lineFn_eq hssin htsin
      (sin_ne_zero_of_abs_lt (sub_ne_zero.2 hne) (by linarith) (by linarith)) _ _
  · refine volume_setOf_lineFn_eq hshalf htsin (ne_of_gt ?_) _ _
    exact sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

/-! ## The three pieces are intervals -/

/-- The left endpoint of every piece of the `t`-wall: the inner corner `x_K(t)`. -/
def cornerX (h : ℝ → ℝ) (t : ℝ) : ℝ := cos t * (h t - 1) - sin t * (h (t + π / 2) - 1)

/-- `H¹`-length of the `d_{t−δ}` piece, divided by `sin t`. -/
def lenL (h : ℝ → ℝ) (t δ : ℝ) : ℝ :=
  (sin δ * (h t - 1) + cos δ * (h (t + π / 2) - 1) - (h (t - δ + π / 2) - 1)) / cos δ

/-- `H¹`-length of the `d_{t+δ}` piece, divided by `sin t`. -/
def lenR (h : ℝ → ℝ) (t δ : ℝ) : ℝ :=
  (-(sin δ) * (h t - 1) + cos δ * (h (t + π / 2) - 1) - (h (t + δ + π / 2) - 1)) / cos δ

/-- `H¹`-length of the `S` piece, divided by `sin t`. -/
def lenS (h : ℝ → ℝ) (t δ : ℝ) : ℝ :=
  (2 * (1 - cos δ) - (h (t + δ) + h (t - δ) - 2 * h t * cos δ)) / sin δ

section Pieces

variable {h : ℝ → ℝ} {t δ : ℝ} (hδ : 0 < δ) (ht0 : 0 < t - δ) (ht2 : t + δ < π / 2)

include hδ ht0 ht2

private lemma tsin : 0 < sin t := by
  have hpi := pi_gt_three
  exact sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

private lemma dcos : 0 < cos δ := by
  have hpi := pi_gt_three
  exact cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

private lemma dsin : 0 < sin δ := by
  have hpi := pi_gt_three
  exact sin_pos_of_pos_of_lt_pi hδ (by linarith)

private lemma thalfsin : 0 < sin (t + π / 2) := by
  have hpi := pi_gt_three
  rw [Real.sin_add_pi_div_two]
  exact cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

private lemma tmhalfsin : 0 < sin (t - δ + π / 2) := by
  have hpi := pi_gt_three
  rw [Real.sin_add_pi_div_two]
  exact cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

private lemma tphalfsin : 0 < sin (t + δ + π / 2) := by
  have hpi := pi_gt_three
  rw [Real.sin_add_pi_div_two]
  exact cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

private lemma tmsin : 0 < sin (t - δ) := by
  have hpi := pi_gt_three
  exact sin_pos_of_pos_of_lt_pi ht0 (by linarith)

private lemma tpsin : 0 < sin (t + δ) := by
  have hpi := pi_gt_three
  exact sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

end Pieces

lemma setOf_wall_le_pos {s₁ s₂ : ℝ} (h1 : 0 < sin s₁) (h2 : 0 < sin s₂)
    (hd : 0 < sin (s₁ - s₂)) (h : ℝ → ℝ) :
    {x : ℝ | wall h s₁ x ≤ wall h s₂ x}
      = Iic ((sin s₁ * (h s₂ - 1) - sin s₂ * (h s₁ - 1)) / sin (s₁ - s₂)) :=
  setOf_lineFn_le_pos h1 h2 hd _ _

lemma setOf_wall_le_neg {s₁ s₂ : ℝ} (h1 : 0 < sin s₁) (h2 : 0 < sin s₂)
    (hd : sin (s₁ - s₂) < 0) (h : ℝ → ℝ) :
    {x : ℝ | wall h s₁ x ≤ wall h s₂ x}
      = Ici ((sin s₁ * (h s₂ - 1) - sin s₂ * (h s₁ - 1)) / sin (s₁ - s₂)) :=
  setOf_lineFn_le_neg h1 h2 hd _ _

section Intervals

variable {h : ℝ → ℝ} {t δ : ℝ} (hδ : 0 < δ) (ht0 : 0 < t - δ) (ht2 : t + δ < π / 2)

include hδ ht0 ht2

/-- The "corner half-line": where the `t`-wall is below the `t`-wall of the other direction. -/
theorem setOf_wall_le_half : {x : ℝ | wall h t x ≤ wall h (t + π / 2) x} = Ici (cornerX h t) := by
  have hd : sin (t - (t + π / 2)) = -1 := by
    rw [show t - (t + π / 2) = -(π / 2) by ring, Real.sin_neg, Real.sin_pi_div_two]
  rw [setOf_wall_le_neg (tsin hδ ht0 ht2) (thalfsin hδ ht0 ht2) (by rw [hd]; norm_num) h, hd]
  congr 1
  rw [cornerX, Real.sin_add_pi_div_two]
  ring

theorem pieceL_eq :
    pieceL h t δ = Icc (cornerX h t) (cornerX h t + sin t * lenL h t δ) := by
  have hcd := dcos hδ ht0 ht2
  have hd : sin (t - δ + π / 2 - t) = cos δ := by
    rw [show t - δ + π / 2 - t = π / 2 - δ by ring, Real.sin_pi_div_two_sub]
  have h2 : {x : ℝ | wall h (t - δ + π / 2) x ≤ wall h t x}
      = Iic (cornerX h t + sin t * lenL h t δ) := by
    rw [setOf_wall_le_pos (tmhalfsin hδ ht0 ht2) (tsin hδ ht0 ht2) (by rw [hd]; exact hcd) h, hd]
    congr 1
    simp only [cornerX, lenL]
    rw [Real.sin_add_pi_div_two, Real.cos_sub]
    field_simp
    ring
  rw [pieceL, Set.ofPred_and, setOf_wall_le_half hδ ht0 ht2, h2, Ici_inter_Iic]

theorem pieceR_eq :
    pieceR h t δ = Icc (cornerX h t) (cornerX h t + sin t * lenR h t δ) := by
  have hcd := dcos hδ ht0 ht2
  have hd : sin (t + δ + π / 2 - t) = cos δ := by
    rw [show t + δ + π / 2 - t = δ + π / 2 by ring, Real.sin_add_pi_div_two]
  have h2 : {x : ℝ | wall h (t + δ + π / 2) x ≤ wall h t x}
      = Iic (cornerX h t + sin t * lenR h t δ) := by
    rw [setOf_wall_le_pos (tphalfsin hδ ht0 ht2) (tsin hδ ht0 ht2) (by rw [hd]; exact hcd) h, hd]
    congr 1
    simp only [cornerX, lenR]
    rw [Real.sin_add_pi_div_two, Real.cos_add]
    field_simp
    ring
  rw [pieceR, Set.ofPred_and, setOf_wall_le_half hδ ht0 ht2, h2, Ici_inter_Iic]

/-- The left endpoint of the `S` piece. -/
theorem pieceS_eq :
    pieceS h t δ
      = Icc ((sin t * (h (t - δ) - 1) - sin (t - δ) * (h t - 1)) / sin δ)
        ((sin t * (h (t - δ) - 1) - sin (t - δ) * (h t - 1)) / sin δ + sin t * lenS h t δ) := by
  have hsd := dsin hδ ht0 ht2
  have hdm : sin (t - δ - t) = -sin δ := by
    rw [show t - δ - t = -δ by ring, Real.sin_neg]
  have hdp : sin (t + δ - t) = sin δ := by rw [show t + δ - t = δ by ring]
  have h1 : {x : ℝ | wall h (t - δ) x ≤ wall h t x}
      = Ici ((sin t * (h (t - δ) - 1) - sin (t - δ) * (h t - 1)) / sin δ) := by
    rw [setOf_wall_le_neg (tmsin hδ ht0 ht2) (tsin hδ ht0 ht2) (by rw [hdm]; linarith) h, hdm]
    congr 1
    field_simp
    ring
  have h2 : {x : ℝ | wall h (t + δ) x ≤ wall h t x}
      = Iic ((sin t * (h (t - δ) - 1) - sin (t - δ) * (h t - 1)) / sin δ + sin t * lenS h t δ) := by
    rw [setOf_wall_le_pos (tpsin hδ ht0 ht2) (tsin hδ ht0 ht2) (by rw [hdp]; exact hsd) h, hdp]
    congr 1
    simp only [lenS]
    rw [Real.sin_add, Real.sin_sub]
    field_simp
    ring
  rw [pieceS, Set.ofPred_and, h1, h2, Ici_inter_Iic]

theorem volume_pieceL : volume (pieceL h t δ) = ENNReal.ofReal (sin t * lenL h t δ) := by
  rw [pieceL_eq hδ ht0 ht2, Real.volume_Icc]
  congr 1; ring

theorem volume_pieceR : volume (pieceR h t δ) = ENNReal.ofReal (sin t * lenR h t δ) := by
  rw [pieceR_eq hδ ht0 ht2, Real.volume_Icc]
  congr 1; ring

theorem volume_pieceS : volume (pieceS h t δ) = ENNReal.ofReal (sin t * lenS h t δ) := by
  rw [pieceS_eq hδ ht0 ht2, Real.volume_Icc]
  congr 1; ring

end Intervals

/-! ## The bound on the niche side -/

/-- **The geometric core of Baek Theorem 6.3.3.**  The `x`-projection of the niche side with
normal `t` is covered by three intervals whose lengths are explicit in the support values. -/
theorem volume_actR_le {Θ : Finset ℝ} (hΘ : Θ.Nonempty)
    (hrange : ∀ s ∈ Θ, 0 < s ∧ s < π / 2) (h : ℝ → ℝ) {t δ : ℝ}
    (hδ : 0 < δ) (ht0 : 0 < t - δ) (ht2 : t + δ < π / 2)
    (ht : t ∈ Θ) (htm : t - δ ∈ Θ) (htp : t + δ ∈ Θ) :
    volume {x : ℝ | roofR Θ hΘ h x = wall h t x}
      ≤ ENNReal.ofReal (sin t * max 0 (lenL h t δ)) + ENNReal.ofReal (sin t * max 0 (lenR h t δ))
        + ENNReal.ofReal (sin t * max 0 (lenS h t δ)) := by
  have hst : 0 < sin t := tsin hδ ht0 ht2
  refine le_trans (measure_mono (actR_subset_pieces hΘ h htm htp)) ?_
  have step : ∀ A B C D : Set ℝ, volume (A ∪ B ∪ C ∪ D)
      ≤ volume A + volume B + volume C + volume D := by
    intro A B C D
    calc volume (A ∪ B ∪ C ∪ D) ≤ volume (A ∪ B ∪ C) + volume D := measure_union_le _ _
      _ ≤ volume (A ∪ B) + volume C + volume D := by
          gcongr; exact measure_union_le _ _
      _ ≤ volume A + volume B + volume C + volume D := by
          gcongr; exact measure_union_le _ _
  refine le_trans (step _ _ _ _) ?_
  rw [volume_crossSet hrange h ht, zero_add, volume_pieceL hδ ht0 ht2,
    volume_pieceR hδ ht0 ht2, volume_pieceS hδ ht0 ht2]
  refine add_le_add (add_le_add ?_ ?_) ?_ <;>
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (le_max_right _ _) hst.le)

theorem volumeReal_subset_actR_le {Θ : Finset ℝ} (hΘ : Θ.Nonempty)
    (hrange : ∀ s ∈ Θ, 0 < s ∧ s < π / 2) (h : ℝ → ℝ) {t δ : ℝ}
    (hδ : 0 < δ) (ht0 : 0 < t - δ) (ht2 : t + δ < π / 2)
    (ht : t ∈ Θ) (htm : t - δ ∈ Θ) (htp : t + δ ∈ Θ)
    {S : Set ℝ} (hS : S ⊆ {x : ℝ | roofR Θ hΘ h x = wall h t x}) :
    volume.real S
      ≤ sin t * max 0 (lenL h t δ) + sin t * max 0 (lenR h t δ)
        + sin t * max 0 (lenS h t δ) := by
  have hst : 0 < sin t := tsin hδ ht0 ht2
  have hbound := le_trans (measure_mono hS) (volume_actR_le hΘ hrange h hδ ht0 ht2 ht htm htp)
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at hbound
  exact hbound

/-! ## The cap side: `σ_K(t) ≤ (h(t+δ) + h(t−δ) − 2h(t)cos δ)/sin δ`

The classical polygon edge-length formula, but only as the **inequality** that needs no adjacency
argument: `actU(t)` is contained in the interval cut out by the two neighbouring supporting
lines. -/

/-- The classical edge-length expression for the polygon edge with normal `t`. -/
def lenU (h : ℝ → ℝ) (t δ : ℝ) : ℝ := (h (t + δ) + h (t - δ) - 2 * h t * cos δ) / sin δ

/-- The `t`-roof piece cut out by the two neighbouring supporting lines. -/
def pieceU (h : ℝ → ℝ) (t δ : ℝ) : Set ℝ :=
  {x : ℝ | lineFn t (h t) x ≤ lineFn (t + δ) (h (t + δ)) x ∧
    lineFn t (h t) x ≤ lineFn (t - δ) (h (t - δ)) x}

section CapPiece

variable {h : ℝ → ℝ} {t δ : ℝ} (hδ : 0 < δ) (ht0 : 0 < t - δ) (ht2 : t + δ < π / 2)

include hδ ht0 ht2

theorem pieceU_eq :
    pieceU h t δ
      = Icc ((sin (t + δ) * h t - sin t * h (t + δ)) / sin δ)
        ((sin (t + δ) * h t - sin t * h (t + δ)) / sin δ + sin t * lenU h t δ) := by
  have hsd := dsin hδ ht0 ht2
  have hdp : sin (t - (t + δ)) = -sin δ := by
    rw [show t - (t + δ) = -δ by ring, Real.sin_neg]
  have hdm : sin (t - (t - δ)) = sin δ := by rw [show t - (t - δ) = δ by ring]
  have h1 : {x : ℝ | lineFn t (h t) x ≤ lineFn (t + δ) (h (t + δ)) x}
      = Ici ((sin (t + δ) * h t - sin t * h (t + δ)) / sin δ) := by
    rw [setOf_lineFn_le_neg (tsin hδ ht0 ht2) (tpsin hδ ht0 ht2) (by rw [hdp]; linarith) _ _, hdp]
    congr 1
    field_simp
    ring
  have h2 : {x : ℝ | lineFn t (h t) x ≤ lineFn (t - δ) (h (t - δ)) x}
      = Iic ((sin (t + δ) * h t - sin t * h (t + δ)) / sin δ + sin t * lenU h t δ) := by
    rw [setOf_lineFn_le_pos (tsin hδ ht0 ht2) (tmsin hδ ht0 ht2) (by rw [hdm]; exact hsd) _ _, hdm]
    congr 1
    simp only [lenU]
    rw [Real.sin_add, Real.sin_sub]
    field_simp
    ring
  rw [pieceU, Set.ofPred_and, h1, h2, Ici_inter_Iic]

theorem volume_pieceU : volume (pieceU h t δ) = ENNReal.ofReal (sin t * lenU h t δ) := by
  rw [pieceU_eq hδ ht0 ht2, Real.volume_Icc]
  congr 1; ring

end CapPiece

/-- `actU(t)` is contained in the piece cut out by the two neighbouring supporting lines. -/
theorem actU_subset_pieceU {ω : ℝ} {Θ : Finset ℝ} (h : ℝ → ℝ) {t δ : ℝ}
    (htm : t - δ ∈ diamondFin ω Θ) (htp : t + δ ∈ diamondFin ω Θ) :
    actU ω Θ h t ⊆ pieceU h t δ := by
  intro x hx
  have hx' : roofU ω Θ h x = lineFn t (h t) x := hx
  refine ⟨?_, ?_⟩
  · rw [← hx']
    exact Finset.inf'_le (fun s => lineFn s (h s) x) htp
  · rw [← hx']
    exact Finset.inf'_le (fun s => lineFn s (h s) x) htm

theorem sigmaH_le_lenU {ω : ℝ} {Θ : Finset ℝ} (h : ℝ → ℝ) {t δ : ℝ}
    (hδ : 0 < δ) (ht0 : 0 < t - δ) (ht2 : t + δ < π / 2)
    (htm : t - δ ∈ diamondFin ω Θ) (htp : t + δ ∈ diamondFin ω Θ) :
    sigmaH ω Θ h t ≤ max 0 (lenU h t δ) := by
  have hst : 0 < sin t := tsin hδ ht0 ht2
  have hsub : actU ω Θ h t ∩ posU ω Θ h ⊆ pieceU h t δ :=
    Set.inter_subset_left.trans (actU_subset_pieceU h htm htp)
  have hfin : volume (pieceU h t δ) ≠ ⊤ := by
    rw [volume_pieceU hδ ht0 ht2]; exact ENNReal.ofReal_ne_top
  have hmono := measureReal_mono hsub hfin
  simp only [measureReal_def] at hmono
  rw [volume_pieceU hδ ht0 ht2] at hmono
  have hle : (ENNReal.ofReal (sin t * lenU h t δ)).toReal ≤ sin t * max 0 (lenU h t δ) := by
    rcases le_or_gt 0 (lenU h t δ) with hpos | hneg
    · rw [ENNReal.toReal_ofReal (by positivity), max_eq_right hpos]
    · rw [ENNReal.ofReal_of_nonpos (by nlinarith), ENNReal.toReal_zero,
        max_eq_left hneg.le, mul_zero]
  rw [sigmaH, div_le_iff₀ hst]
  calc volume.real (actU ω Θ h t ∩ posU ω Θ h)
      ≤ (ENNReal.ofReal (sin t * lenU h t δ)).toReal := hmono
    _ ≤ sin t * max 0 (lenU h t δ) := hle
    _ = max 0 (lenU h t δ) * sin t := by ring

/-! ## The `tauH` dictionary for `ω = π/2` -/

lemma floorF_pi_div_two (h : ℝ → ℝ) (x : ℝ) :
    floorF (π / 2) h x = lineFn (π / 2) (h (π / 2) - 1) x := by
  have hfan : fanFin (π / 2) = ({π / 2} : Finset ℝ) := by
    rw [fanFin]; exact Finset.insert_eq_self.2 (Finset.mem_singleton_self _)
  rw [floorF]
  simp [hfan]

lemma volume_floorF_eq (h : ℝ → ℝ) {t : ℝ} (ht0 : 0 < t) (ht2 : t < π / 2) (c : ℝ) :
    volume {x : ℝ | floorF (π / 2) h x = lineFn t c x} = 0 := by
  have hpi := pi_gt_three
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 (by linarith)
  have he : {x : ℝ | floorF (π / 2) h x = lineFn t c x}
      = {x : ℝ | lineFn (π / 2) (h (π / 2) - 1) x = lineFn t c x} := by
    ext x
    rw [mem_ofPred_eq, mem_ofPred_eq, floorF_pi_div_two]
  rw [he]
  refine volume_setOf_lineFn_eq (by rw [Real.sin_pi_div_two]; norm_num) hst (ne_of_gt ?_) _ _
  exact sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

lemma volume_actF_pi_div_two (h : ℝ → ℝ) {t : ℝ} (ht0 : 0 < t) (ht2 : t < π / 2) :
    volume (actF (π / 2) h t) = 0 := volume_floorF_eq h ht0 ht2 (h t - 1)

theorem tauH_eq_pi_div_two {Θ : Finset ℝ} (hΘ : Θ.Nonempty) (h : ℝ → ℝ) {t : ℝ}
    (ht0 : 0 < t) (ht2 : t < π / 2) :
    tauH (π / 2) Θ hΘ h t = volume.real (actR Θ hΘ h t ∩ posR (π / 2) Θ hΘ h) / sin t := by
  have hnull := volume_actF_pi_div_two h ht0 ht2
  have h1 : volume.real (actF (π / 2) h t ∩ posU (π / 2) Θ h) = 0 := by
    rw [measureReal_def, measure_mono_null Set.inter_subset_left hnull, ENNReal.toReal_zero]
  have h2 : volume.real (actF (π / 2) h t ∩ posR (π / 2) Θ hΘ h) = 0 := by
    rw [measureReal_def, measure_mono_null Set.inter_subset_left hnull, ENNReal.toReal_zero]
  rw [tauH, h1, h2]
  ring_nf

/-! ## `lenL`, `lenR` and the arm lengths

For a *polygon* cap the edge with normal `s` ends exactly at the intersection with the adjacent
supporting line, which is what Baek's Lemma 6.3.2 uses.  Only the **easy** direction of that
identity is needed here, and it holds for every compact convex body:
`v^+_K(s) ∈ K ⊆ H_K(s+δ)` gives `m^+_K(s) ≤ (h(s+δ) − h(s)cos δ)/sin δ`. -/

theorem edgeMax_le {K : Set ℝ²} (hK : IsCompact K) (hne : K.Nonempty) (s d : ℝ)
    (hd : 0 < sin d) :
    edgeMax K s ≤ (supportFn K (s + d) - supportFn K s * cos d) / sin d := by
  have hmem := vtxP_mem hK hne s
  have hle := le_supportFn hK hmem (s + d)
  rw [vtxP, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u_add,
    inner_v_u_add] at hle
  rw [le_div_iff₀ hd]
  linarith

theorem le_edgeMin {K : Set ℝ²} (hK : IsCompact K) (hne : K.Nonempty) (s d : ℝ)
    (hd : 0 < sin d) :
    (supportFn K s * cos d - supportFn K (s - d)) / sin d ≤ edgeMin K s := by
  have hmem := vtxM_mem hK hne s
  have hle := le_supportFn hK hmem (s - d)
  rw [show s - d = s + -d by ring] at hle
  rw [vtxM, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u_add,
    inner_v_u_add, Real.cos_neg, Real.sin_neg] at hle
  rw [div_le_iff₀ hd, show s - d = s + -d by ring]
  linarith

lemma armGm_eq_add (K : Set ℝ²) (t : ℝ) :
    armGm K t = supportFn K t + edgeMin K (t + π / 2) := by
  rw [armGm, inner_sub_left, inner_outerCorner_u, ← inner_vtxM_v]
  have hv : v (t + π / 2) = -u t := v_add_pi_div_two t
  rw [hv, inner_neg_right]
  ring

section ArmCompare

variable {K : Set ℝ²} (hK : IsCompact K) (hne : K.Nonempty) {t δ : ℝ}
  (hδ : 0 < δ) (ht0 : 0 < t - δ) (ht2 : t + δ < π / 2)

include hK hne hδ ht0 ht2

theorem lenR_le :
    lenR (supportFn K) t δ
      ≤ sin δ / cos δ * (1 - armGp K t + (1 - cos δ) / sin δ) := by
  have hsd := dsin hδ ht0 ht2
  have hcd := dcos hδ ht0 ht2
  have hE := edgeMax_le hK hne (t + π / 2) δ hsd
  have key : sin δ / cos δ * (1 - (supportFn K t + edgeMax K (t + π / 2)) + (1 - cos δ) / sin δ)
      - lenR (supportFn K) t δ
      = sin δ / cos δ * ((supportFn K (t + π / 2 + δ) - supportFn K (t + π / 2) * cos δ) / sin δ
          - edgeMax K (t + π / 2)) := by
    rw [lenR, show t + δ + π / 2 = t + π / 2 + δ by ring]
    field_simp
    ring
  have hpos : 0 ≤ sin δ / cos δ
      * ((supportFn K (t + π / 2 + δ) - supportFn K (t + π / 2) * cos δ) / sin δ
        - edgeMax K (t + π / 2)) :=
    mul_nonneg (div_pos hsd hcd).le (sub_nonneg.2 hE)
  rw [armGp_eq_add]
  linarith [key, hpos]

theorem lenL_le :
    lenL (supportFn K) t δ
      ≤ sin δ / cos δ * (armGm K t - 1 + (1 - cos δ) / sin δ) := by
  have hsd := dsin hδ ht0 ht2
  have hcd := dcos hδ ht0 ht2
  have hE := le_edgeMin hK hne (t + π / 2) δ hsd
  have key : sin δ / cos δ * ((supportFn K t + edgeMin K (t + π / 2)) - 1 + (1 - cos δ) / sin δ)
      - lenL (supportFn K) t δ
      = sin δ / cos δ * (edgeMin K (t + π / 2)
          - (supportFn K (t + π / 2) * cos δ - supportFn K (t + π / 2 - δ)) / sin δ) := by
    rw [lenL, show t - δ + π / 2 = t + π / 2 - δ by ring]
    field_simp
    ring
  have hpos : 0 ≤ sin δ / cos δ * (edgeMin K (t + π / 2)
      - (supportFn K (t + π / 2) * cos δ - supportFn K (t + π / 2 - δ)) / sin δ) :=
    mul_nonneg (div_pos hsd hcd).le (sub_nonneg.2 hE)
  rw [armGm_eq_add]
  linarith [key, hpos]

end ArmCompare

/-! ## The arithmetic of Baek's two cases -/

/-- The purely arithmetic core of Theorem 6.3.3: from the three interval bounds, the cap-side
bound, and `g⁻ ≤ g⁺`, one gets `σ ≤ k₀(g⁺)·tan δ + O(δ²)`. -/
theorem thm633_arith {s gp gm lL lR lS lU thalf tand : ℝ}
    (hsum : s ≤ max 0 lL + max 0 lR + max 0 lS) (hlU : s ≤ max 0 lU)
    (hlS : lS = 2 * thalf - lU)
    (hlL : lL ≤ tand * (gm - 1 + thalf)) (hlR : lR ≤ tand * (1 - gp + thalf))
    (hgm : gm ≤ gp) (hthalf : 0 ≤ thalf) (htan : 0 ≤ tand) :
    s ≤ k0 gp * tand + (2 * tand * thalf + max 0 (thalf - tand / 2)) := by
  have hk0 := k0_nonneg gp
  have hkabs := abs_le_k0 gp
  have hkhalf := half_le_k0 gp
  have habs : |gp - 1| = |1 - gp| := abs_sub_comm gp 1
  have hm1 : max 0 (thalf - tand / 2) ≥ 0 := le_max_left _ _
  rcases lt_or_ge lU 0 with hU | hU
  · -- degenerate: the cap side is empty, so `σ = 0`
    have : s ≤ 0 := le_trans hlU (le_of_eq (max_eq_left hU.le))
    nlinarith [mul_nonneg hk0 htan, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) htan) hthalf]
  -- the main case
  have hsU : s ≤ lU := le_trans hlU (le_of_eq (max_eq_right hU))
  -- bound the two `d`-pieces
  have hLb : max 0 lL ≤ tand * (max 0 (gm - 1) + thalf) := by
    refine max_le (by positivity) (le_trans hlL ?_)
    have : gm - 1 + thalf ≤ max 0 (gm - 1) + thalf := by linarith [le_max_right 0 (gm - 1)]
    nlinarith
  have hRb : max 0 lR ≤ tand * (max 0 (1 - gp) + thalf) := by
    refine max_le (by positivity) (le_trans hlR ?_)
    have : 1 - gp + thalf ≤ max 0 (1 - gp) + thalf := by linarith [le_max_right 0 (1 - gp)]
    nlinarith
  have hsplit : max 0 (gm - 1) + max 0 (1 - gp) ≤ |1 - gp| := by
    rcases le_or_gt gp 1 with hg | hg
    · rw [max_eq_left (by linarith [le_abs_self (gm - 1)] : gm - 1 ≤ 0),
        max_eq_right (by linarith : (0:ℝ) ≤ 1 - gp), abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - gp)]
      linarith
    · rw [max_eq_left (by linarith : (1:ℝ) - gp ≤ 0), abs_of_nonpos (by linarith : 1 - gp ≤ 0)]
      have : max 0 (gm - 1) ≤ gp - 1 := max_le (by linarith) (by linarith)
      linarith
  have hP : max 0 lL + max 0 lR ≤ tand * (|1 - gp| + 2 * thalf) := by nlinarith
  -- the `S`-piece
  have hSb : max 0 lS ≤ max 0 (2 * thalf - s) := by
    rw [hlS]
    exact max_le_max le_rfl (by linarith)
  rw [habs] at hkabs hkhalf
  rcases le_or_gt s (2 * thalf) with hcase | hcase
  · rw [show max 0 (2 * thalf - s) = 2 * thalf - s from max_eq_right (by linarith)] at hSb
    have h2 : 2 * s ≤ tand * (|1 - gp| + 2 * thalf) + 2 * thalf := by linarith
    have hkey : |1 - gp| * tand / 2 + tand / 2 ≤ k0 gp * tand := by nlinarith
    linarith [le_max_right 0 (thalf - tand / 2), mul_nonneg htan hthalf]
  · rw [show max 0 (2 * thalf - s) = 0 from max_eq_left (by linarith)] at hSb
    have hle : s ≤ tand * (|1 - gp| + 2 * thalf) := by linarith
    have hkey : |1 - gp| * tand ≤ k0 gp * tand := by nlinarith
    linarith [hm1]

/-! ## Theorem 6.3.3 for interior angles -/

lemma sigmaH_nonneg {ω : ℝ} {Θ : Finset ℝ} (h : ℝ → ℝ) {t : ℝ} (ht : 0 < sin t) :
    0 ≤ sigmaH ω Θ h t := div_nonneg measureReal_nonneg ht.le

lemma armGm_le_armGp {K : Set ℝ²} (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    armGm K t ≤ armGp K t := by
  rw [armGm_eq_add, armGp_eq_add]
  linarith [edgeMin_le_edgeMax hK hne (t + π / 2)]

/-- **Baek Theorem 6.3.3** for an *interior* angle `t` of a maximum polygon cap with rotation
angle `π/2` (see `blueprint/ch3-8.md` §19.4 for the two extreme angles).  The error term is
written out exactly; `2 tan δ · tan(δ/2) + (tan(δ/2) − tan δ/2)⁺ = O(δ²)`. -/
theorem sigmaH_le_k0_armGp {Θ : Finset ℝ} (hP : PolySetup (π / 2) Θ) {K : Set ℝ²}
    (hKc : IsCompact K) (hKne : K.Nonempty) (hK : IsMaxPolyCap (π / 2) Θ K) {t δ : ℝ}
    (hδ : 0 < δ) (ht0 : 0 < t - δ) (ht2 : t + δ < π / 2)
    (ht : t ∈ Θ) (htm : t - δ ∈ Θ) (htp : t + δ ∈ Θ) :
    sigmaH (π / 2) Θ (supportFn K) t
      ≤ k0 (armGp K t) * (sin δ / cos δ)
        + (2 * (sin δ / cos δ) * ((1 - cos δ) / sin δ)
          + max 0 ((1 - cos δ) / sin δ - (sin δ / cos δ) / 2)) := by
  have hst : 0 < sin t := tsin hδ ht0 ht2
  have hsd : 0 < sin δ := dsin hδ ht0 ht2
  have hcd : 0 < cos δ := dcos hδ ht0 ht2
  have hrange : ∀ s ∈ Θ, 0 < s ∧ s < π / 2 := fun s hs => hP.angles.2 s hs
  set h := supportFn K with hh
  -- balancedness turns the cap side into the niche side
  have hbal := hK.balanced (hP := hP) (mem_diamondFin_of_mem ht)
  have hτ := tauH_eq_pi_div_two hP.angles.1 h (hrange t ht).1 (hrange t ht).2
  have hsub : actR Θ hP.angles.1 h t ∩ posR (π / 2) Θ hP.angles.1 h
      ⊆ {x : ℝ | roofR Θ hP.angles.1 h x = wall h t x} := Set.inter_subset_left
  have hmain : sigmaH (π / 2) Θ h t
      ≤ max 0 (lenL h t δ) + max 0 (lenR h t δ) + max 0 (lenS h t δ) := by
    rw [hbal, hτ, div_le_iff₀ hst]
    have := volumeReal_subset_actR_le hP.angles.1 hrange h hδ ht0 ht2 ht htm htp hsub
    nlinarith [this]
  have hU := sigmaH_le_lenU (ω := π / 2) h hδ ht0 ht2
    (mem_diamondFin_of_mem htm) (mem_diamondFin_of_mem htp)
  have hlS : lenS h t δ = 2 * ((1 - cos δ) / sin δ) - lenU h t δ := by
    rw [lenS, lenU]; field_simp
  exact thm633_arith hmain hU hlS (lenL_le hKc hKne hδ ht0 ht2)
    (lenR_le hKc hKne hδ ht0 ht2) (armGm_le_armGp hKc hKne t)
    (div_nonneg (by linarith [Real.cos_le_one δ]) hsd.le) (div_nonneg hsd.le hcd.le)

/-! ## Making the `O(δ²)` explicit -/

lemma tan_le_add_cube {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : sin δ / cos δ ≤ δ + δ ^ 3 := by
  have hpi := pi_gt_three
  have hcd : 0 < cos δ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcos := Real.one_sub_sq_div_two_le_cos (x := δ)
  have hs : sin δ ≤ δ := (Real.sin_lt hδ).le
  have hsq1 : δ ^ 2 ≤ 1 := by nlinarith [hδ.le, hδ1]
  have hcube : δ ^ 5 ≤ δ ^ 3 := by
    calc δ ^ 5 = δ ^ 3 * δ ^ 2 := by ring
      _ ≤ δ ^ 3 * 1 := mul_le_mul_of_nonneg_left hsq1 (pow_nonneg hδ.le 3)
      _ = δ ^ 3 := by ring
  have hmul : (δ + δ ^ 3) * (1 - δ ^ 2 / 2) ≤ (δ + δ ^ 3) * cos δ :=
    mul_le_mul_of_nonneg_left hcos (by positivity)
  rw [div_le_iff₀ hcd]
  nlinarith [hmul, hs, hcube]

lemma le_tan_self {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : δ ≤ sin δ / cos δ := by
  have hpi := pi_gt_three
  have h := Real.lt_tan hδ (by linarith)
  rw [Real.tan_eq_sin_div_cos] at h
  exact h.le

lemma thalf_le_add_cube {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - cos δ) / sin δ ≤ δ / 2 + δ ^ 3 / 2 := by
  have hpi := pi_gt_three
  have hcd : 0 < cos δ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsd : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδ (by linarith)
  have hcos := Real.one_sub_sq_div_two_le_cos (x := δ)
  have htan : δ ≤ sin δ / cos δ := le_tan_self hδ hδ1
  have hsin : δ * cos δ ≤ sin δ := by
    rw [le_div_iff₀ hcd] at htan; linarith
  have h1 : (δ / 2 + δ ^ 3 / 2) * (δ * cos δ) ≤ (δ / 2 + δ ^ 3 / 2) * sin δ :=
    mul_le_mul_of_nonneg_left hsin (by positivity)
  have h2 : δ ^ 2 / 2 * ((1 + δ ^ 2) * (1 - δ ^ 2 / 2)) ≤ (δ / 2 + δ ^ 3 / 2) * (δ * cos δ) := by
    have hfac : (δ / 2 + δ ^ 3 / 2) * (δ * cos δ) = δ ^ 2 / 2 * ((1 + δ ^ 2) * cos δ) := by ring
    rw [hfac]
    have : (1 + δ ^ 2) * (1 - δ ^ 2 / 2) ≤ (1 + δ ^ 2) * cos δ :=
      mul_le_mul_of_nonneg_left hcos (by positivity)
    nlinarith [this, sq_nonneg δ]
  have hsq1 : δ ^ 2 ≤ 1 := by nlinarith [hδ.le, hδ1]
  have h3 : δ ^ 2 / 2 ≤ δ ^ 2 / 2 * ((1 + δ ^ 2) * (1 - δ ^ 2 / 2)) := by
    have hnn : (0:ℝ) ≤ δ ^ 4 / 4 * (1 - δ ^ 2) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith [hnn]
  rw [div_le_iff₀ hsd]
  linarith

/-- **Baek Theorem 6.3.3** with an explicit `O(δ²)`: for an interior angle of a maximum polygon
cap with rotation angle `π/2` and step `δ ≤ 1`,

    `σ_K(t) ≤ k₀(g⁺_K(t))·δ + (k₀(g⁺_K(t)) + 5)·δ²`. -/
theorem sigmaH_le_k0_delta {Θ : Finset ℝ} (hP : PolySetup (π / 2) Θ) {K : Set ℝ²}
    (hKc : IsCompact K) (hKne : K.Nonempty) (hK : IsMaxPolyCap (π / 2) Θ K) {t δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht0 : 0 < t - δ) (ht2 : t + δ < π / 2)
    (ht : t ∈ Θ) (htm : t - δ ∈ Θ) (htp : t + δ ∈ Θ) :
    sigmaH (π / 2) Θ (supportFn K) t
      ≤ k0 (armGp K t) * δ + (k0 (armGp K t) + 5) * δ ^ 2 := by
  have hpi := pi_gt_three
  have hcd : 0 < cos δ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsd : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδ (by linarith)
  have hk0 := k0_nonneg (armGp K t)
  have hmain := sigmaH_le_k0_armGp hP hKc hKne hK hδ ht0 ht2 ht htm htp
  have htan1 : sin δ / cos δ ≤ δ + δ ^ 3 := tan_le_add_cube hδ hδ1
  have htan2 : sin δ / cos δ ≤ 2 * δ := by
    rw [← Real.tan_eq_sin_div_cos]; exact tan_le_two_mul hδ.le hδ1
  have htan3 : δ ≤ sin δ / cos δ := le_tan_self hδ hδ1
  have hth : (1 - cos δ) / sin δ ≤ δ / 2 + δ ^ 3 / 2 := thalf_le_add_cube hδ hδ1
  have hth0 : 0 ≤ (1 - cos δ) / sin δ :=
    div_nonneg (by linarith [Real.cos_le_one δ]) hsd.le
  have hcube : δ ^ 3 ≤ δ := by nlinarith [hδ.le, hδ1, sq_nonneg δ]
  have hcube2 : δ ^ 3 ≤ δ ^ 2 := by nlinarith [hδ.le, hδ1, sq_nonneg δ]
  have hthδ : (1 - cos δ) / sin δ ≤ δ := by linarith
  have hterm1 : 2 * (sin δ / cos δ) * ((1 - cos δ) / sin δ) ≤ 4 * δ ^ 2 := by
    nlinarith [htan2, hthδ, hth0, div_nonneg hsd.le hcd.le]
  have hterm2 : max 0 ((1 - cos δ) / sin δ - (sin δ / cos δ) / 2) ≤ δ ^ 2 / 2 := by
    refine max_le (by positivity) ?_
    linarith [hth, htan3, hcube2]
  have hterm0 : k0 (armGp K t) * (sin δ / cos δ) ≤ k0 (armGp K t) * δ + k0 (armGp K t) * δ ^ 2 := by
    have h1 : k0 (armGp K t) * (sin δ / cos δ) ≤ k0 (armGp K t) * (δ + δ ^ 3) :=
      mul_le_mul_of_nonneg_left htan1 hk0
    nlinarith [h1, hk0, hcube2]
  nlinarith [hmain, hterm0, hterm1, hterm2, sq_nonneg δ]

/-! ## `edgeLength ≤ σ`: the polygon edge really is the active set

`sigmaH` is defined as `|actU(t) ∩ posU| / sin t`; the geometric edge `e_K(t)` projects into
`actU(t)`, and lands in `posU` except at the single point where the fan floor meets the `t`-line.
-/

theorem ofReal_edgeLength_mul_sin_le {Θ : Finset ℝ} (hP : PolySetup (π / 2) Θ) {K : Set ℝ²}
    (hK : IsPolyCap (π / 2) Θ K) {t : ℝ} (ht : t ∈ Θ) :
    ENNReal.ofReal (edgeLength K t * sin t)
      ≤ volume (actU (π / 2) Θ (supportFn K) t ∩ posU (π / 2) Θ (supportFn K)) := by
  have hpi := pi_gt_three
  obtain ⟨ht0, ht2⟩ := hP.angles.2 t ht
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 (by linarith)
  set h := supportFn K with hh
  set A := vtxP K t with hA
  set B := vtxM K t with hB
  have hKc := hK.1.isCompact
  have hKne := hK.1.nonempty
  have hAB : B 0 - A 0 = edgeLength K t * sin t := by
    have hsub := congrArg (fun p : ℝ² => p 0) (vtxP_sub_vtxM K t)
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, v_coord_zero] at hsub
    linarith [hsub]
  -- the open projection of the edge, minus one point, is inside `actU ∩ posU`
  have hkey : Ioo (A 0) (B 0) \ {x : ℝ | floorF (π / 2) h x = lineFn t (h t) x}
      ⊆ actU (π / 2) Θ h t ∩ posU (π / 2) Θ h := by
    rintro x ⟨hx, hxF⟩
    have hlen : 0 < B 0 - A 0 := by linarith [hx.1, hx.2]
    set l := (x - A 0) / (B 0 - A 0) with hl
    have hl0 : 0 ≤ l := div_nonneg (by linarith [hx.1]) hlen.le
    have hl1 : l ≤ 1 := by rw [hl, div_le_one hlen]; linarith [hx.2]
    have hlmul : l * (B 0 - A 0) = x - A 0 := by
      rw [hl]; field_simp
    set p := (1 - l) • A + l • B with hp
    have hpe : p ∈ edge K t :=
      (convex_edge hK.1.convex t) (vtxP_mem_edge hKc hKne t) (vtxM_mem_edge hKc hKne t)
        (by linarith) hl0 (by ring)
    have hp0 : p 0 = x := by
      simp only [hp, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      nlinarith [hlmul]
    have hpin : ⟪p, u t⟫ = h t := hpe.2
    have hpK : p ∈ capH (π / 2) Θ h := by
      rw [capH_supportFn hP hK]; exact hpe.1
    have h5 : p 1 = lineFn t (h t) x := by
      rw [← hp0]
      exact le_antisymm ((le_lineFn_iff hst (h t) p).2 (le_of_eq hpin))
        ((lineFn_le_iff hst (h t) p).2 (le_of_eq hpin.symm))
    have hup : roofU (π / 2) Θ h x = lineFn t (h t) x := by
      have h2 : p 1 ≤ roofU (π / 2) Θ h (p 0) := hpK.2
      have h3 : roofU (π / 2) Θ h x ≤ lineFn t (h t) x :=
        Finset.inf'_le (fun s => lineFn s (h s) x) (mem_diamondFin_of_mem ht)
      rw [hp0, h5] at h2
      linarith
    refine ⟨hup, ?_⟩
    show floorF (π / 2) h x < roofU (π / 2) Θ h x
    have h4 : floorF (π / 2) h (p 0) ≤ p 1 := hpK.1
    rw [hp0, h5] at h4
    rw [hup]
    rcases lt_or_eq_of_le h4 with hlt | heq
    · exact hlt
    · exact absurd (show floorF (π / 2) h x = lineFn t (h t) x from heq) hxF
  have hnull := volume_floorF_eq h ht0 ht2 (h t)
  calc ENNReal.ofReal (edgeLength K t * sin t)
      = volume (Ioo (A 0) (B 0)) := by rw [Real.volume_Ioo, hAB]
    _ = volume (Ioo (A 0) (B 0) \ {x : ℝ | floorF (π / 2) h x = lineFn t (h t) x}) :=
        (measure_sdiff_null hnull).symm
    _ ≤ volume (actU (π / 2) Θ h t ∩ posU (π / 2) Θ h) := measure_mono hkey

theorem edgeLength_le_sigmaH {Θ : Finset ℝ} (hP : PolySetup (π / 2) Θ) {K : Set ℝ²}
    (hK : IsPolyCap (π / 2) Θ K) {t : ℝ} (ht : t ∈ Θ) :
    edgeLength K t ≤ sigmaH (π / 2) Θ (supportFn K) t := by
  have hpi := pi_gt_three
  obtain ⟨ht0, ht2⟩ := hP.angles.2 t ht
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 (by linarith)
  have hfin : volume (actU (π / 2) Θ (supportFn K) t ∩ posU (π / 2) Θ (supportFn K)) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_right) ?_)
    rw [posU_eq_Ioo hP hK, Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  have hle := (ENNReal.ofReal_le_iff_le_toReal hfin).1 (ofReal_edgeLength_mul_sin_le hP hK ht)
  rw [sigmaH, le_div_iff₀ hst, measureReal_def]
  exact hle

/-- **Baek Theorem 6.3.3**, in the form used by §6.4: a bound on the *edge length*
`σ_K({t}) = |e_K(t)|` of a maximum polygon cap at an interior angle. -/
theorem edgeLength_le_k0_delta {Θ : Finset ℝ} (hP : PolySetup (π / 2) Θ) {K : Set ℝ²}
    (hK : IsMaxPolyCap (π / 2) Θ K) {t δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht0 : 0 < t - δ) (ht2 : t + δ < π / 2)
    (ht : t ∈ Θ) (htm : t - δ ∈ Θ) (htp : t + δ ∈ Θ) :
    edgeLength K t ≤ k0 (armGp K t) * δ + (k0 (armGp K t) + 5) * δ ^ 2 :=
  le_trans (edgeLength_le_sigmaH hP hK.1 ht)
    (sigmaH_le_k0_delta hP hK.1.1.isCompact hK.1.1.nonempty hK hδ hδ1 ht0 ht2 ht htm htp)

/-- The same bound for the surface area measure of the singleton `{t}` (Thm 2.1.1). -/
theorem sigmaK_singleton_le_k0_delta {Θ : Finset ℝ} (hP : PolySetup (π / 2) Θ) {K : Set ℝ²}
    (hK : IsMaxPolyCap (π / 2) Θ K) {t δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ht0 : 0 < t - δ) (ht2 : t + δ < π / 2)
    (ht : t ∈ Θ) (htm : t - δ ∈ Θ) (htp : t + δ ∈ Θ) :
    sigmaK K {t} ≤ ENNReal.ofReal (k0 (armGp K t) * δ + (k0 (armGp K t) + 5) * δ ^ 2) := by
  rw [sigmaK_singleton hK.1.1.isCompact hK.1.1.nonempty]
  exact ENNReal.ofReal_le_ofReal (edgeLength_le_k0_delta hP hK hδ hδ1 ht0 ht2 ht htm htp)

/-! ## The face lemma: a polygon has no edge in a non-normal direction

This is the foundation of §6.4 (see `blueprint/ch3-8.md` §23): for `K = ⋂_{r ∈ A} H_K(r)` with `A`
finite, the supporting line in a direction not among the `u_r` touches `K` in a single point. -/

lemma u_frame (s r : ℝ) : u r = cos (r - s) • u s + sin (r - s) • v s := by
  have h1 : ⟪u r, u s⟫ = cos (r - s) := by
    rw [real_inner_comm]; exact inner_u_u_sub s r
  have h2 : ⟪u r, v s⟫ = sin (r - s) := by
    rw [real_inner_comm]; exact inner_v_u_eq_sin s r
  conv_lhs => rw [decomp_u_v s (u r)]
  rw [h1, h2]

lemma supportFn_congr_of_u_eq (S : Set ℝ²) {a b : ℝ} (h : u a = u b) :
    supportFn S a = supportFn S b := by
  rw [supportFn, supportFn]
  congr 1
  ext y
  constructor <;> rintro ⟨p, hp, rfl⟩ <;> exact ⟨p, hp, by rw [proj, proj, h]⟩

/-- **The face lemma.** -/
theorem edgeLength_eq_zero_of_no_normal {K : Set ℝ²} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hconv : Convex ℝ K) {A : Finset ℝ} (hA : K = ⋂ r ∈ A, hpLe r (supportFn K r))
    {s : ℝ} (hs : ∀ r ∈ A, u r ≠ u s)
    (hwidth : 0 < supportFn K s + supportFn K (s + π)) :
    edgeLength K s = 0 := by
  classical
  by_contra hL
  have hLpos : 0 < edgeLength K s :=
    lt_of_le_of_ne (edgeLength_nonneg hKc hKne s) (Ne.symm hL)
  set P := vtxP K s with hP
  set M := vtxM K s with hM
  set m : ℝ² := (1 / 2 : ℝ) • P + (1 / 2 : ℝ) • M with hm
  have hPK : P ∈ K := vtxP_mem hKc hKne s
  have hMK : M ∈ K := vtxM_mem hKc hKne s
  have hmK : m ∈ K := hconv hPK hMK (by norm_num) (by norm_num) (by norm_num)
  have hPs : ⟪P, u s⟫ = supportFn K s := inner_vtxP_u K s
  have hMs : ⟪M, u s⟫ = supportFn K s := inner_vtxM_u K s
  have hms : ⟪m, u s⟫ = supportFn K s := by
    rw [hm, inner_add_left, real_inner_smul_left, real_inner_smul_left, hPs, hMs]; ring
  by_cases hact : ∃ r ∈ A, ⟪m, u r⟫ = supportFn K r
  · -- an active constraint must be parallel to `u_s`
    obtain ⟨r, hrA, hr⟩ := hact
    have hPr : ⟪P, u r⟫ ≤ supportFn K r := le_supportFn hKc hPK r
    have hMr : ⟪M, u r⟫ ≤ supportFn K r := le_supportFn hKc hMK r
    have hmr : ⟪m, u r⟫ = (⟪P, u r⟫ + ⟪M, u r⟫) / 2 := by
      rw [hm, inner_add_left, real_inner_smul_left, real_inner_smul_left]; ring
    have hPeq : ⟪P, u r⟫ = supportFn K r := by rw [hmr] at hr; linarith
    have hMeq : ⟪M, u r⟫ = supportFn K r := by rw [hmr] at hr; linarith
    have hdiff : ⟪P - M, u r⟫ = 0 := by rw [inner_sub_left, hPeq, hMeq]; ring
    rw [vtxP_sub_vtxM, real_inner_smul_left] at hdiff
    have hvr : ⟪v s, u r⟫ = 0 := by
      rcases mul_eq_zero.1 hdiff with h | h
      · exact absurd h (ne_of_gt hLpos)
      · exact h
    have hsin : sin (r - s) = 0 := by rwa [inner_v_u_eq_sin] at hvr
    have hcos : cos (r - s) = 1 ∨ cos (r - s) = -1 := by
      have := sin_sq_add_cos_sq (r - s)
      rw [hsin] at this
      have : (cos (r - s) - 1) * (cos (r - s) + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hcos with hc | hc
    · exact hs r hrA (by rw [u_frame s r, hc, hsin]; module)
    · -- `u_r = −u_s = u_{s+π}`: the width in direction `s` would be zero
      have hur : u r = u (s + π) := by
        rw [u_frame s r, hc, hsin, u_add_pi]; module
      have : supportFn K r = supportFn K (s + π) := supportFn_congr_of_u_eq K hur
      have hmrv : ⟪m, u r⟫ = -supportFn K s := by
        rw [hur, show u (s + π) = -u s from u_add_pi s, inner_neg_right, hms]
      rw [hmrv, this] at hr
      linarith
  · -- no active constraint: `m` is interior, contradicting maximality of `⟪·, u_s⟫`
    push Not at hact
    have hlt : ∀ r ∈ A, ⟪m, u r⟫ < supportFn K r := fun r hr =>
      lt_of_le_of_ne (le_supportFn hKc hmK r) (hact r hr)
    set ε : ℝ := if hA' : A.Nonempty then A.inf' hA' (fun r => supportFn K r - ⟪m, u r⟫) else 1
      with hε
    have hε0 : 0 < ε := by
      rw [hε]
      split_ifs with hA'
      · rw [Finset.lt_inf'_iff]
        exact fun r hr => by linarith [hlt r hr]
      · norm_num
    have hεle : ∀ r ∈ A, ε ≤ supportFn K r - ⟪m, u r⟫ := by
      intro r hr
      rw [hε]
      have hA' : A.Nonempty := ⟨r, hr⟩
      rw [dif_pos hA']
      exact Finset.inf'_le _ hr
    have hmem : m + ε • u s ∈ K := by
      rw [hA]
      refine mem_iInter₂.2 fun r hr => ?_
      show ⟪m + ε • u s, u r⟫ ≤ supportFn K r
      rw [inner_add_left, real_inner_smul_left]
      have h1 : ⟪u s, u r⟫ ≤ 1 := by
        have := real_inner_le_norm (u s) (u r)
        rwa [norm_u, norm_u, one_mul] at this
      nlinarith [hεle r hr, hε0]
    have := le_supportFn hKc hmem s
    rw [inner_add_left, real_inner_smul_left, inner_u_u, mul_one, hms] at this
    linarith

/-- `p ↦ ⟪p, w⟫` as a linear map. -/
def innerLin (w : ℝ²) : ℝ² →ₗ[ℝ] ℝ where
  toFun p := ⟪p, w⟫
  map_add' x y := inner_add_left x y w
  map_smul' c x := by simp [real_inner_smul_left]

@[simp] lemma innerLin_apply (w p : ℝ²) : innerLin w p = ⟪p, w⟫ := rfl

/-- A line is null. -/
lemma volume_setOf_inner_eq (s c : ℝ) : volume {p : ℝ² | ⟪p, u s⟫ = c} = 0 := by
  have hker : {p : ℝ² | ⟪p, u s⟫ = 0} = (LinearMap.ker (innerLin (u s)) : Set ℝ²) := by
    ext q; simp [LinearMap.mem_ker]
  have hnull : volume {p : ℝ² | ⟪p, u s⟫ = 0} = 0 := by
    rw [hker]
    refine Measure.addHaar_submodule volume _ ?_
    intro htop
    have hmem : u s ∈ LinearMap.ker (innerLin (u s)) := by rw [htop]; trivial
    rw [LinearMap.mem_ker, innerLin_apply, inner_u_u] at hmem
    exact one_ne_zero hmem
  have himg : {p : ℝ² | ⟪p, u s⟫ = c} = tr (c • u s) {p : ℝ² | ⟪p, u s⟫ = 0} := by
    ext p
    rw [mem_tr, mem_ofPred_eq, mem_ofPred_eq, inner_sub_left, real_inner_smul_left, inner_u_u,
      mul_one]
    constructor <;> intro h <;> linarith
  rw [himg, volume_tr, hnull]

/-- A body of positive area has positive width in every direction. -/
lemma width_pos_of_volume_ne_zero {K : Set ℝ²} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hvol : volume K ≠ 0) (s : ℝ) : 0 < supportFn K s + supportFn K (s + π) := by
  obtain ⟨p, hp⟩ := hKne
  have h1 : ⟪p, u s⟫ ≤ supportFn K s := le_supportFn hKc hp s
  have h2 : ⟪p, u (s + π)⟫ ≤ supportFn K (s + π) := le_supportFn hKc hp (s + π)
  rw [u_add_pi, inner_neg_right] at h2
  rcases lt_or_eq_of_le (by linarith : (0:ℝ) ≤ supportFn K s + supportFn K (s + π)) with h | h
  · exact h
  · exfalso
    refine hvol (measure_mono_null (fun q hq => ?_) (volume_setOf_inner_eq s (supportFn K s)))
    have e1 : ⟪q, u s⟫ ≤ supportFn K s := le_supportFn hKc hq s
    have e2 : ⟪q, u (s + π)⟫ ≤ supportFn K (s + π) := le_supportFn hKc hq (s + π)
    rw [u_add_pi, inner_neg_right] at e2
    show ⟪q, u s⟫ = supportFn K s
    linarith

/-! ## A polygon vertex in a non-normal direction is an intersection of two supporting lines -/

/-- If `Q` maximizes `⟪·, u_t⟫` over the polygon `K` and `d` is a direction that does not violate
any active constraint, then `⟪d, u_t⟫ ≤ 0`. -/
private lemma inner_dir_nonpos_of_max {K : Set ℝ²} (hKc : IsCompact K) {A : Finset ℝ}
    (hA : K = ⋂ r ∈ A, hpLe r (supportFn K r)) {Q d : ℝ²} (hQ : Q ∈ K)
    (hd : ∀ r ∈ A, ⟪Q, u r⟫ < supportFn K r ∨ ⟪d, u r⟫ ≤ 0)
    {t : ℝ} (hQt : ⟪Q, u t⟫ = supportFn K t) : ⟪d, u t⟫ ≤ 0 := by
  classical
  by_contra hdt
  push Not at hdt
  set f : ℝ → ℝ := fun r => if 0 < ⟪d, u r⟫ then (supportFn K r - ⟪Q, u r⟫) / ⟪d, u r⟫ else 1
    with hf
  set ε : ℝ := if hA' : A.Nonempty then min 1 (A.inf' hA' f) else 1 with hε
  have hfpos : ∀ r ∈ A, 0 < f r := by
    intro r hr
    simp only [hf]
    split_ifs with hdr
    · refine div_pos ?_ hdr
      rcases hd r hr with h | h
      · linarith
      · linarith
    · norm_num
  have hε0 : 0 < ε := by
    rw [hε]
    split_ifs with hA'
    · exact lt_min one_pos ((Finset.lt_inf'_iff _).2 hfpos)
    · norm_num
  have hεle : ∀ r ∈ A, ε ≤ f r := by
    intro r hr
    have hA' : A.Nonempty := ⟨r, hr⟩
    rw [hε, dif_pos hA']
    exact le_trans (min_le_right _ _) (Finset.inf'_le f hr)
  have hmem : Q + ε • d ∈ K := by
    rw [hA]
    refine mem_iInter₂.2 fun r hr => ?_
    show ⟪Q + ε • d, u r⟫ ≤ supportFn K r
    rw [inner_add_left, real_inner_smul_left]
    by_cases hdr : 0 < ⟪d, u r⟫
    · have h1 := hεle r hr
      rw [hf] at h1
      simp only [if_pos hdr] at h1
      rw [le_div_iff₀ hdr] at h1
      linarith
    · push Not at hdr
      have := mul_nonpos_of_nonneg_of_nonpos hε0.le hdr
      have h2 : ⟪Q, u r⟫ ≤ supportFn K r := le_supportFn hKc hQ r
      linarith
  have := le_supportFn hKc hmem t
  rw [inner_add_left, real_inner_smul_left, hQt] at this
  nlinarith [hε0, hdt]

/-- **Every vertex of a polygon in a non-normal direction is `v_K(r, r')` for two normals.** -/
theorem vtxP_mem_vtx2_image {K : Set ℝ²} (hKc : IsCompact K) (hKne : K.Nonempty)
    {A : Finset ℝ} (hA : K = ⋂ r ∈ A, hpLe r (supportFn K r))
    (hwidth : ∀ s, 0 < supportFn K s + supportFn K (s + π))
    {t : ℝ} (ht : ∀ r ∈ A, u r ≠ u t) :
    ∃ r ∈ A, ∃ r' ∈ A, sin (r' - r) ≠ 0 ∧ vtxP K t = vtx2 K r r' := by
  classical
  set Q := vtxP K t with hQdef
  have hQK : Q ∈ K := vtxP_mem hKc hKne t
  have hQt : ⟪Q, u t⟫ = supportFn K t := inner_vtxP_u K t
  -- every active normal is non-parallel to `u_t`
  have hact_sin : ∀ r ∈ A, ⟪Q, u r⟫ = supportFn K r → sin (r - t) ≠ 0 := by
    intro r hr hQr hsin
    have hcos : cos (r - t) = 1 ∨ cos (r - t) = -1 := by
      have h := sin_sq_add_cos_sq (r - t)
      rw [hsin] at h
      have h2 : (cos (r - t) - 1) * (cos (r - t) + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hcos with hc | hc
    · exact ht r hr (by rw [u_frame t r, hc, hsin]; module)
    · have hur : u r = u (t + π) := by rw [u_frame t r, hc, hsin, u_add_pi]; module
      have h1 : supportFn K r = supportFn K (t + π) := supportFn_congr_of_u_eq K hur
      rw [hur, show u (t + π) = -u t from u_add_pi t, inner_neg_right, hQt] at hQr
      have := hwidth t
      linarith
  -- there are two active normals with non-parallel directions
  have hkey : ∃ r ∈ A, ∃ r' ∈ A, ⟪Q, u r⟫ = supportFn K r ∧ ⟪Q, u r'⟫ = supportFn K r' ∧
      sin (r' - r) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    -- first: some constraint is active
    obtain ⟨r₀, hr₀, hr₀eq⟩ : ∃ r ∈ A, ⟪Q, u r⟫ = supportFn K r := by
      by_contra hno
      push Not at hno
      have := inner_dir_nonpos_of_max hKc hA hQK
        (fun r hr => Or.inl (lt_of_le_of_ne (le_supportFn hKc hQK r) (hno r hr))) hQt (d := u t)
      rw [inner_u_u] at this
      linarith
    -- all active normals are parallel to `u_{r₀}`; push along `v_{r₀}`
    have hsin0 : sin (r₀ - t) ≠ 0 := hact_sin r₀ hr₀ hr₀eq
    have hdir : ∀ (c : ℝ), (∀ r ∈ A, ⟪Q, u r⟫ < supportFn K r ∨ ⟪c • v r₀, u r⟫ ≤ 0) →
        ⟪c • v r₀, u t⟫ ≤ 0 := fun c hc => inner_dir_nonpos_of_max hKc hA hQK hc hQt
    have hzero : ∀ r ∈ A, ⟪Q, u r⟫ = supportFn K r → ⟪v r₀, u r⟫ = 0 := by
      intro r hr hre
      have hs := hcon r₀ hr₀ r hr hr₀eq hre
      rw [inner_v_u_eq_sin]
      exact hs
    have h1 := hdir 1 (fun r hr => by
      rcases eq_or_lt_of_le (le_supportFn hKc hQK r) with he | hl
      · exact Or.inr (by rw [one_smul, hzero r hr he])
      · exact Or.inl hl)
    have h2 := hdir (-1) (fun r hr => by
      rcases eq_or_lt_of_le (le_supportFn hKc hQK r) with he | hl
      · exact Or.inr (by rw [real_inner_smul_left, hzero r hr he, mul_zero])
      · exact Or.inl hl)
    rw [one_smul] at h1
    rw [real_inner_smul_left] at h2
    rw [inner_v_u_eq_sin] at h1 h2
    have : sin (t - r₀) = 0 := le_antisymm h1 (by linarith)
    have hne : sin (t - r₀) ≠ 0 := by
      intro hz
      refine hsin0 ?_
      rw [show r₀ - t = -(t - r₀) by ring, Real.sin_neg, hz, neg_zero]
    exact hne this
  obtain ⟨r, hr, r', hr', hQr, hQr', hsin⟩ := hkey
  refine ⟨r, hr, r', hr', hsin, ?_⟩
  -- the two active constraints determine `Q`
  have hdec := decomp_u_v r Q
  have hvr : ⟪Q, v r⟫ = (supportFn K r' - supportFn K r * cos (r' - r)) / sin (r' - r) := by
    have h := congrArg (fun p : ℝ² => ⟪p, u r'⟫) hdec
    simp only [inner_add_left, real_inner_smul_left] at h
    rw [inner_u_u_sub, inner_v_u_eq_sin, hQr, hQr'] at h
    field_simp at h ⊢
    linarith [h]
  rw [vtx2, ← hvr, ← hQr]
  exact hdec

/-! ## The vertex is constant on a gap between normals -/

/-- A continuous real function on an interval with finite image is constant (IVT). -/
lemma const_of_continuousOn_of_finite_image {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hfin : (f '' Icc a b).Finite) :
    ∀ t ∈ Icc a b, f t = f a := by
  intro t ht
  by_contra hne
  have hmono : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hcont : ContinuousOn f (Icc a t) := hf.mono hmono
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `f t < f a`
    have hsub : Icc (f t) (f a) ⊆ f '' Icc a b :=
      le_trans (intermediate_value_Icc' ht.1 hcont) (Set.image_mono hmono)
    exact ((Set.Icc_infinite hlt).mono hsub) hfin
  · have hsub : Icc (f a) (f t) ⊆ f '' Icc a b :=
      le_trans (intermediate_value_Icc ht.1 hcont) (Set.image_mono hmono)
    exact ((Set.Icc_infinite hgt).mono hsub) hfin

section Gap

variable {K : Set ℝ²} (hKc : IsCompact K) (hKne : K.Nonempty) (hconv : Convex ℝ K)
  {A : Finset ℝ} (hA : K = ⋂ r ∈ A, hpLe r (supportFn K r))
  (hwidth : ∀ s, 0 < supportFn K s + supportFn K (s + π))
  {a b : ℝ} (hgap : ∀ t ∈ Icc a b, ∀ r ∈ A, u r ≠ u t)

include hKc hKne hconv hA hwidth hgap

lemma vtxP_eq_vtxM_on_gap : ∀ t ∈ Icc a b, vtxP K t = vtxM K t := by
  intro t ht
  have h0 : edgeLength K t = 0 :=
    edgeLength_eq_zero_of_no_normal hKc hKne hconv hA (hgap t ht) (hwidth t)
  have := vtxP_sub_vtxM K t
  rw [h0, zero_smul, sub_eq_zero] at this
  exact this

lemma continuousOn_vtxP_gap : ContinuousOn (vtxP K) (Icc a b) := by
  intro t ht
  have hL : ContinuousWithinAt (vtxP K) (Icc a t) t := by
    refine ContinuousWithinAt.congr
      ((continuousWithinAt_vtxM hKc hKne t).mono Icc_subset_Iic_self) (fun y hy => ?_) ?_
    · exact (vtxP_eq_vtxM_on_gap hKc hKne hconv hA hwidth hgap y ⟨hy.1, le_trans hy.2 ht.2⟩)
    · exact vtxP_eq_vtxM_on_gap hKc hKne hconv hA hwidth hgap t ht
  have hR : ContinuousWithinAt (vtxP K) (Icc t b) t :=
    (continuousWithinAt_vtxP hKc hKne t).mono Icc_subset_Ici_self
  have hU := hL.union hR
  refine hU.mono ?_
  intro y hy
  rcases le_or_gt y t with h | h
  · exact Or.inl ⟨hy.1, h⟩
  · exact Or.inr ⟨h.le, hy.2⟩

/-- **The vertex map is constant on a gap between normals.** -/
theorem vtxP_const_on_gap : ∀ t ∈ Icc a b, vtxP K t = vtxP K a := by
  have hcont := continuousOn_vtxP_gap hKc hKne hconv hA hwidth hgap
  set S := (A ×ˢ A).image (fun q : ℝ × ℝ => vtx2 K q.1 q.2) with hS
  have hmemS : ∀ t ∈ Icc a b, vtxP K t ∈ S := by
    intro t ht
    obtain ⟨r, hr, r', hr', -, he⟩ :=
      vtxP_mem_vtx2_image hKc hKne hA hwidth (hgap t ht)
    exact Finset.mem_image.2 ⟨(r, r'), Finset.mem_product.2 ⟨hr, hr'⟩, he.symm⟩
  have hw : ∀ w : ℝ², ∀ t ∈ Icc a b, ⟪vtxP K t, w⟫ = ⟪vtxP K a, w⟫ := by
    intro w
    refine const_of_continuousOn_of_finite_image
      ((continuous_id.inner continuous_const).comp_continuousOn hcont) ?_
    refine Set.Finite.subset (Set.Finite.image (fun p : ℝ² => ⟪p, w⟫) S.finite_toSet) ?_
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨vtxP K s, hmemS s hs, rfl⟩
  intro t ht
  ext i
  fin_cases i
  · have h := hw (u 0) t ht
    rwa [inner_u_zero, inner_u_zero] at h
  · have h := hw (u (π / 2)) t ht
    rwa [inner_u_pi_div_two, inner_u_pi_div_two] at h

/-- **`σ_K` gives no mass to a gap between normals.** -/
theorem sigmaK_gap_eq_zero (hab : a ≤ b) : sigmaK K (Ioc a b) = 0 := by
  have hQ := vtxP_const_on_gap hKc hKne hconv hA hwidth hgap
  have hint : (∫ s in (0:ℝ)..b, supportFn K s) - ∫ s in (0:ℝ)..a, supportFn K s
      = ∫ s in a..b, supportFn K s :=
    intervalIntegral.integral_interval_sub_left (integrable_supportFn hKc hKne 0 b)
      (integrable_supportFn hKc hKne 0 a)
  have heq : (∫ s in a..b, supportFn K s) = ⟪vtxP K a, v a⟫ - ⟪vtxP K a, v b⟫ := by
    rw [← integral_inner_u (vtxP K a) a b]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hab] at hs
    rw [← hQ s hs, inner_vtxP_u]
  have harc : arcFn K b - arcFn K a = 0 := by
    rw [arcFn, arcFn, hQ b (right_mem_Icc.2 hab), hQ a (left_mem_Icc.2 hab)]
    linarith [hint, heq]
  rw [sigmaK_Ioc hKc hKne, harc, ENNReal.ofReal_zero]

end Gap
