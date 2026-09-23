/-
# Sofa/GerverArea.lean — Baek Thm 8.4.6: `𝒬(K, B_K, D_K) = A(K)` for Gerver's cap, without Green's theorem

Baek proves Theorem 8.4.6 by integrating over the Jordan curve that bounds the niche of Gerver's
sofa (Thm 8.4.1 (2)): `|N(K)| = J(x|_{[φ^R, φ^L]}) − J(B) − J(D)`.  Here we use the three regions of
our Green-free proof of Theorem 8.2.4 (§33–§34 of the blueprint):

* `R₁ = conv(B_K ∪ {W^R_K}) \ B_K` with `|R₁| = J(X_B, W^R) − J(b_B)` (tangent-cap formula),
* `R₂ = conv(D_K ∪ {Z^L_K}) \ D_K` with `|R₂| = J(Z^L, Y_D) − J(d_D)`,
* `Ω = {Z^L < ξ < W^R, 0 < η < U(ξ)}` under the roof `U = d | c | b`, with
  `|Ω| = ∫ U⁺ = J(W^R, x^R) + J(x|_I) + J(x^L, Z^L)` once `U ≥ 0`,

and show `N(K) ∩ H̆^R ⊆ R₁`, `N(K) ∩ H̆^L ⊆ R₂`, `N(K) \ H̆^R \ H̆^L ⊆ Ω ∪ {floor}` from the
description of the niche in Thm 8.4.1 (2): every point of `N(K)` lies strictly below the boundary
curve `D⁻¹ · x · B⁻¹` at its own abscissa (`GerverNiche.below`), and the core lies in the closure of
the niche (`GerverNiche.core_closure`).  With the matching ends `X_B = x^R`, `Y_D = x^L`
(Thm 8.4.3) the segment terms cancel and `|N(K)| ≤ J(x|_I) − J(b_B) − J(d_D)`, i.e.
`𝒬(K, B_K, D_K) ≤ A(K)`; the reverse inequality is Theorem 8.2.4.

STATUS: [PROOF-C-local] round 34 (2026-09-23, Opus 5.5).
-/
import Sofa.GerverFaces

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace Interval

namespace Sofa

variable {K : Set ℝ²} {φ θ : ℝ} {Bc Dc : ℝ → ℝ²}

/-! ## Segments in coordinates -/

/-- A point on the line `⟪·, n⟫ = c` (not horizontal: `n 0 ≠ 0`) between two points of the line,
in the second coordinate, lies on the segment between them. -/
lemma mem_segment_of_line {a b q n : ℝ²} (hn : n 0 ≠ 0) (ha : ⟪a, n⟫ = ⟪q, n⟫)
    (hb : ⟪b, n⟫ = ⟪q, n⟫) (h1 : a 1 ≤ q 1) (h2 : q 1 ≤ b 1) :
    q ∈ segment ℝ a b := by
  rcases eq_or_lt_of_le (h1.trans h2) with hab | hab
  · -- degenerate: `q = a`
    have e1 : a 1 = q 1 := le_antisymm h1 (by rw [hab]; exact h2)
    have e0 : a 0 = q 0 := by
      simp only [inner_eq] at ha
      rw [e1] at ha
      exact mul_right_cancel₀ hn (by linarith)
    have : q = a := by
      ext i; fin_cases i
      · exact e0.symm
      · exact e1.symm
    rw [this]; exact left_mem_segment ℝ a b
  set s := (q 1 - a 1) / (b 1 - a 1) with hs
  have hd : 0 < b 1 - a 1 := by linarith
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hd.le
  have hs1 : s ≤ 1 := (div_le_one hd).2 (by linarith)
  refine ⟨1 - s, s, by linarith, hs0, by ring, ?_⟩
  have e1 : (1 - s) * a 1 + s * b 1 = q 1 := by
    rw [hs]; field_simp; ring
  simp only [inner_eq] at ha hb
  have e0 : (1 - s) * a 0 + s * b 0 = q 0 := by
    have : ((1 - s) * a 0 + s * b 0) * n 0 = q 0 * n 0 := by
      linear_combination (1 - s) * ha + s * hb - n 1 * e1
    exact mul_right_cancel₀ hn this
  ext i
  fin_cases i
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; exact e0
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; exact e1

/-- The horizontal version: points of a line `⟪·, n⟫ = c` with `n 1 ≠ 0`, ordered by the first
coordinate. -/
lemma mem_segment_of_line' {a b q n : ℝ²} (hn : n 1 ≠ 0) (ha : ⟪a, n⟫ = ⟪q, n⟫)
    (hb : ⟪b, n⟫ = ⟪q, n⟫) (h1 : a 0 ≤ q 0) (h2 : q 0 ≤ b 0) :
    q ∈ segment ℝ a b := by
  rcases eq_or_lt_of_le (h1.trans h2) with hab | hab
  · -- degenerate: `q = a`
    have e0 : a 0 = q 0 := le_antisymm h1 (by rw [hab]; exact h2)
    have e1 : a 1 = q 1 := by
      simp only [inner_eq] at ha
      rw [e0] at ha
      exact mul_right_cancel₀ hn (by linarith)
    have : q = a := by
      ext i; fin_cases i
      · exact e0.symm
      · exact e1.symm
    rw [this]; exact left_mem_segment ℝ a b
  set s := (q 0 - a 0) / (b 0 - a 0) with hs
  have hd : 0 < b 0 - a 0 := by linarith
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hd.le
  have hs1 : s ≤ 1 := (div_le_one hd).2 (by linarith)
  refine ⟨1 - s, s, by linarith, hs0, by ring, ?_⟩
  have e0 : (1 - s) * a 0 + s * b 0 = q 0 := by
    rw [hs]; field_simp; ring
  simp only [inner_eq] at ha hb
  have e1 : (1 - s) * a 1 + s * b 1 = q 1 := by
    have : ((1 - s) * a 1 + s * b 1) * n 1 = q 1 * n 1 := by
      linear_combination (1 - s) * ha + s * hb - n 0 * e0
    exact mul_right_cancel₀ hn this
  ext i
  fin_cases i
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; exact e0
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; exact e1

/-! ## Monotone coordinates along the tails -/

/-- If `c` is continuous on `[a, b]` with right derivatives `c'` on `[a, b)` and `⟪c', w⟫ ≥ 0`, then
`⟪c, w⟫` is nondecreasing. -/
lemma monotoneOn_inner_of_rightDeriv {c c' : ℝ → ℝ²} {a b : ℝ} (w : ℝ²)
    (hc : ContinuousOn c (Icc a b)) (hd : ∀ t ∈ Ico a b, HasDerivWithinAt c (c' t) (Ici t) t)
    (hpos : ∀ t ∈ Ioo a b, 0 ≤ ⟪c' t, w⟫) : MonotoneOn (fun t => ⟪c t, w⟫) (Icc a b) := by
  refine monotoneOn_Icc_of_rightDeriv_nonneg (F' := fun t => ⟪c' t, w⟫)
    (hc.inner continuousOn_const) (fun t ht => ?_) hpos
  have h1 := ((hd t ⟨ht.1.le, ht.2⟩).mono Ioi_subset_Ici_self).inner (𝕜 := ℝ)
    (hasDerivWithinAt_const t (Ioi t) w)
  rw [inner_zero_right, zero_add] at h1
  exact h1

theorem GerverTails.B_x_mono (hG : GerverTails φ θ K Bc Dc) :
    MonotoneOn (fun t => Bc t 0) (Icc (π / 2 - θ) (π / 2)) := by
  have hpi := pi_pos
  have hθ := hG.theta_lt
  obtain ⟨β, hβ⟩ := hG.B_deriv
  have h := monotoneOn_inner_of_rightDeriv (u 0) hG.B_cont (fun t ht => (hβ t ht).2)
    (fun t ht => ?_)
  · intro x hx y hy hxy
    have := h hx hy hxy
    simp only [inner_u_zero] at this
    exact this
  · rw [real_inner_smul_left, inner_v_u_eq_sin, zero_sub, sin_neg]
    have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2])
    nlinarith [(hβ t ⟨ht.1.le, ht.2⟩).1]

theorem GerverTails.B_y_anti (hG : GerverTails φ θ K Bc Dc) :
    AntitoneOn (fun t => Bc t 1) (Icc (π / 2 - θ) (π / 2)) := by
  have hpi := pi_pos
  have hθ := hG.theta_lt
  obtain ⟨β, hβ⟩ := hG.B_deriv
  have h := monotoneOn_inner_of_rightDeriv (-u (π / 2)) hG.B_cont (fun t ht => (hβ t ht).2)
    (fun t ht => ?_)
  · intro x hx y hy hxy
    have := h hx hy hxy
    simp only [inner_neg_right, inner_u_pi_div_two] at this
    linarith
  · rw [inner_neg_right, real_inner_smul_left, inner_v_u_eq_sin, sin_pi_div_two_sub]
    have hc : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2]⟩
    nlinarith [(hβ t ⟨ht.1.le, ht.2⟩).1]

theorem GerverTails.D_x_mono (hG : GerverTails φ θ K Bc Dc) :
    MonotoneOn (fun t => Dc t 0) (Icc 0 θ) := by
  have hpi := pi_pos
  have hθ := hG.theta_lt
  obtain ⟨δ, hδ⟩ := hG.D_deriv
  have h := monotoneOn_inner_of_rightDeriv (u 0) hG.D_cont (fun t ht => (hδ t ht).2)
    (fun t ht => ?_)
  · intro x hx y hy hxy
    have := h hx hy hxy
    simp only [inner_u_zero] at this
    exact this
  · rw [real_inner_smul_left, inner_u_u_eq_cos, sub_zero]
    have hc : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact mul_nonneg (hδ t ⟨ht.1.le, ht.2⟩).1.le hc

theorem GerverTails.D_y_mono (hG : GerverTails φ θ K Bc Dc) :
    MonotoneOn (fun t => Dc t 1) (Icc 0 θ) := by
  have hpi := pi_pos
  have hθ := hG.theta_lt
  obtain ⟨δ, hδ⟩ := hG.D_deriv
  have h := monotoneOn_inner_of_rightDeriv (u (π / 2)) hG.D_cont (fun t ht => (hδ t ht).2)
    (fun t ht => ?_)
  · intro x hx y hy hxy
    have := h hx hy hxy
    simp only [inner_u_pi_div_two] at this
    exact this
  · rw [real_inner_smul_left, inner_u_u_eq_cos, show t - π / 2 = -(π / 2 - t) by ring, cos_neg,
      cos_pi_div_two_sub]
    have hs : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1.le (by linarith [ht.2])
    exact mul_nonneg (hδ t ⟨ht.1.le, ht.2⟩).1.le hs

/-! ## The niche of Gerver's sofa (Thm 8.4.1 (2)) -/

/-- **Baek Theorem 8.4.1 (2), the niche.**  On top of the tails (`GerverTails`), the description
of the niche `N(K)` of Gerver's sofa as the region under the Jordan arc `D⁻¹ · x_K · B⁻¹`:

* the core `x_K|[φ, π/2 − φ]` lies in the closure of `N(K)` (it is part of `∂N(K)`);
* every point of `N(K)` lies strictly below the arc at its own abscissa: below a point of `D`,
  of the core, or of `B` with the same first coordinate.

Baek does not prove Thm 8.4.1 (Rem 8.4.1); these are the only facts about `N(K)` that our proof
of Theorem 8.4.6 uses. -/
structure GerverNiche (φ θ : ℝ) (K : Set ℝ²) (Bc Dc : ℝ → ℝ²) : Prop
    extends GerverTails φ θ K Bc Dc where
  core_closure : ∀ t ∈ Icc φ (π / 2 - φ), innerCorner K t ∈ closure (niche K (π / 2))
  below : ∀ q ∈ niche K (π / 2),
    (∃ t ∈ Icc 0 θ, Dc t 0 = q 0 ∧ q 1 < Dc t 1) ∨
    (∃ t ∈ Icc φ (π / 2 - φ), innerCorner K t 0 = q 0 ∧ q 1 < innerCorner K t 1) ∨
    (∃ t ∈ Icc (π / 2 - θ) (π / 2), Bc t 0 = q 0 ∧ q 1 < Bc t 1)

lemma ptWR_coord_zero (φ : ℝ) (K : Set ℝ²) : ptWR φ K 0 = (supportFn K φ - 1) / cos φ := by
  simp [ptWR]

lemma ptWR_coord_one (φ : ℝ) (K : Set ℝ²) : ptWR φ K 1 = 0 := by
  simp [ptWR]

lemma ptZL_coord_zero (φ : ℝ) (K : Set ℝ²) :
    ptZL φ K 0 = (1 - supportFn K (π - φ)) / cos φ := by
  simp [ptZL_eq_smul]

lemma ptZL_coord_one (φ : ℝ) (K : Set ℝ²) : ptZL φ K 1 = 0 := by
  simp [ptZL_eq_smul]

/-- **(a)** `N(K) ∩ H̆^R_K ⊆ conv(B_K ∪ {W^R_K}) \ B_K`. -/
theorem GerverNiche.niche_inter_right_subset (hG : GerverNiche φ θ K Bc Dc) :
    niche K (π / 2) ∩ hpGe φ (supportFn K φ - 1)
      ⊆ convexHull ℝ (insert (ptWR φ K) (Bset φ K)) \ Bset φ K := by
  have hT := hG.toGerverTails
  have hpi := pi_pos
  have hφ0 := hT.phi_pos
  have hφθ := hT.phi_lt_theta
  have hθ := hT.theta_lt
  have hK := hT.injective
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  rintro q ⟨hqN, hqR⟩
  have hR : supportFn K φ - 1 ≤ ⟪q, u φ⟫ := hqR
  rw [inner_u_decomp] at hR
  have hq1 : 0 ≤ q 1 := (mem_niche_iff.1 hqN).1.1
  rcases hG.below q hqN with ⟨t, ht, hx, hy⟩ | ⟨t, ht, hx, hy⟩ | ⟨t, ht, hx, hy⟩
  · -- below `D`: impossible, `D` lies below and left of `x^L_K ∉ int H̆^R_K`
    exfalso
    have h1 : Dc t 0 ≤ Dc θ 0 := hT.D_x_mono ht ⟨by linarith, le_rfl⟩ ht.2
    have h2 : Dc t 1 ≤ Dc θ 1 := hT.D_y_mono ht ⟨by linarith, le_rfl⟩ ht.2
    rw [hT.D_end, hx] at h1
    rw [hT.D_end] at h2
    have h3 := hK.inner_innerCorner_u_le_right hφ0 (t := π / 2 - φ) (by linarith) (by linarith)
    rw [inner_u_decomp] at h3
    have e1 := mul_le_mul_of_nonneg_right h1 hc.le
    have e2 := mul_lt_mul_of_pos_right (lt_of_lt_of_le hy h2) hs
    linarith
  · -- below the core: impossible, `x_K(t) ∉ int H̆^R_K`
    exfalso
    have h3 := hK.inner_innerCorner_u_le_right hφ0 ht.1 (by linarith [ht.2])
    rw [inner_u_decomp, hx] at h3
    have e2 := mul_lt_mul_of_pos_right hy hs
    linarith
  · -- below `B(t)`
    have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2])
    refine ⟨?_, fun hqB => ?_⟩
    swap
    · -- `q` is strictly inside the wall `b_K(t)`, so `q ∉ B_K`
      have h1 := (mem_Bset.1 hqB).2 t ⟨by linarith [ht.1], ht.2⟩
      have hw := hT.B_wall t ht
      rw [inner_u_decomp] at h1 hw
      rw [hx] at hw
      have e2 := mul_lt_mul_of_pos_right hy hst
      linarith
    set C := convexHull ℝ (insert (ptWR φ K) (Bset φ K)) with hCdef
    have hC : Convex ℝ C := convex_convexHull ℝ _
    have hBC : ∀ s ∈ Icc (π / 2 - θ) (π / 2), Bc s ∈ C := fun s hs =>
      subset_convexHull ℝ _ (mem_insert_of_mem _ (hT.B_mem s hs))
    have hWC : ptWR φ K ∈ C := subset_convexHull ℝ _ (mem_insert _ _)
    have hx1 : Bc (π / 2 - θ) 0 ≤ q 0 := by
      rw [← hx]; exact hT.B_x_mono ⟨le_rfl, by linarith⟩ ht ht.1
    have hx2 : q 0 ≤ Bc (π / 2) 0 := by
      rw [← hx]; exact hT.B_x_mono ht ⟨by linarith, le_rfl⟩ ht.2
    have hvert : ∀ y : ℝ, y ≤ q 1 → (!₂[q 0, y] : ℝ²) ∈ C → q ∈ C := by
      intro y hyq hyC
      refine hC.segment_subset hyC (hBC t ht) ?_
      refine mem_segment_of_line (n := u 0) (by simp) ?_ ?_ ?_ hy.le
      · rw [inner_u_zero, inner_u_zero, vec_coord_zero]
      · rw [inner_u_zero, inner_u_zero, hx]
      · rw [vec_coord_one]; exact hyq
    rcases le_or_gt ((supportFn K φ - 1) / cos φ) (q 0) with hw | hw
    · -- above the floor point `(q₀, 0) ∈ [W^R_K, B(π/2)]`
      refine hvert 0 hq1 ?_
      have hBf : Bc (π / 2) 1 = 0 := by
        have := hT.B_wall (π / 2) ⟨by linarith, le_rfl⟩
        rwa [hK.isCap.supportFn_pi_div_two, sub_self, inner_u_pi_div_two] at this
      refine hC.segment_subset hWC (hBC _ ⟨by linarith, le_rfl⟩) ?_
      refine mem_segment_of_line' (n := u (π / 2)) (by simp) ?_ ?_ ?_ ?_
      · rw [inner_u_pi_div_two, inner_u_pi_div_two, ptWR_coord_one, vec_coord_one]
      · rw [inner_u_pi_div_two, inner_u_pi_div_two, hBf, vec_coord_one]
      · rw [ptWR_coord_zero, vec_coord_zero]; exact hw
      · rw [vec_coord_zero]; exact hx2
    · -- above the point of `b^R_K` below `q`, which lies in `[W^R_K, x^R_K]`
      have hw' : q 0 * cos φ < supportFn K φ - 1 := (lt_div_iff₀ hc).1 hw
      set y := (supportFn K φ - 1 - q 0 * cos φ) / sin φ with hy_def
      have hyr : y * sin φ = supportFn K φ - 1 - q 0 * cos φ := by
        rw [hy_def]; field_simp
      have hxR := inner_innerCorner_u (S := K) φ
      rw [inner_u_decomp] at hxR
      rw [hT.B_start] at hx1
      have e1 := mul_le_mul_of_nonneg_right hx1 hc.le
      refine hvert y (le_of_mul_le_mul_right (by linarith) hs) ?_
      refine hC.segment_subset hWC (hBC _ ⟨le_rfl, by linarith⟩) ?_
      rw [hT.B_start]
      refine mem_segment_of_line (n := u φ) (by rw [u_coord_zero]; exact hc.ne') ?_ ?_ ?_ ?_
      · rw [inner_u_decomp, inner_u_decomp, ptWR_coord_zero, ptWR_coord_one, vec_coord_zero,
          vec_coord_one, div_mul_cancel₀ _ hc.ne']
        linarith
      · rw [inner_u_decomp, inner_u_decomp, vec_coord_zero, vec_coord_one]
        linarith
      · rw [ptWR_coord_one, vec_coord_one, hy_def]
        exact div_nonneg (by linarith) hs.le
      · rw [vec_coord_one]
        exact le_of_mul_le_mul_right (by linarith) hs

/-- **(b)** `N(K) ∩ H̆^L_K ⊆ conv(D_K ∪ {Z^L_K}) \ D_K`. -/
theorem GerverNiche.niche_inter_left_subset (hG : GerverNiche φ θ K Bc Dc) :
    niche K (π / 2) ∩ hpGe (π - φ) (supportFn K (π - φ) - 1)
      ⊆ convexHull ℝ (insert (ptZL φ K) (Dset φ K)) \ Dset φ K := by
  have hT := hG.toGerverTails
  have hpi := pi_pos
  have hφ0 := hT.phi_pos
  have hφθ := hT.phi_lt_theta
  have hθ := hT.theta_lt
  have hK := hT.injective
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  rintro q ⟨hqN, hqL⟩
  have hL : supportFn K (π - φ) - 1 ≤ ⟪q, u (π - φ)⟫ := hqL
  rw [inner_u_decomp, cos_pi_sub, sin_pi_sub] at hL
  have hq1 : 0 ≤ q 1 := (mem_niche_iff.1 hqN).1.1
  rcases hG.below q hqN with ⟨t, ht, hx, hy⟩ | ⟨t, ht, hx, hy⟩ | ⟨t, ht, hx, hy⟩
  · -- below `D(t)`
    have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ⟨?_, fun hqD => ?_⟩
    swap
    · -- `q` is strictly inside the wall `d_K(t)`, so `q ∉ D_K`
      have h1 := (mem_Dset.1 hqD).2 t ⟨ht.1, by linarith [ht.2]⟩
      have hw := hT.D_wall t ht
      rw [inner_u_decomp, cos_add_pi_div_two, sin_add_pi_div_two] at h1 hw
      rw [hx] at hw
      have e2 := mul_lt_mul_of_pos_right hy hct
      linarith
    set C := convexHull ℝ (insert (ptZL φ K) (Dset φ K)) with hCdef
    have hC : Convex ℝ C := convex_convexHull ℝ _
    have hDC : ∀ s ∈ Icc 0 θ, Dc s ∈ C := fun s hs =>
      subset_convexHull ℝ _ (mem_insert_of_mem _ (hT.D_mem s hs))
    have hZC : ptZL φ K ∈ C := subset_convexHull ℝ _ (mem_insert _ _)
    have hx1 : Dc 0 0 ≤ q 0 := by
      rw [← hx]; exact hT.D_x_mono ⟨le_rfl, by linarith⟩ ht ht.1
    have hx2 : q 0 ≤ Dc θ 0 := by
      rw [← hx]; exact hT.D_x_mono ht ⟨by linarith, le_rfl⟩ ht.2
    have hvert : ∀ y : ℝ, y ≤ q 1 → (!₂[q 0, y] : ℝ²) ∈ C → q ∈ C := by
      intro y hyq hyC
      refine hC.segment_subset hyC (hDC t ht) ?_
      refine mem_segment_of_line (n := u 0) (by simp) ?_ ?_ ?_ hy.le
      · rw [inner_u_zero, inner_u_zero, vec_coord_zero]
      · rw [inner_u_zero, inner_u_zero, hx]
      · rw [vec_coord_one]; exact hyq
    rcases le_or_gt (q 0) ((1 - supportFn K (π - φ)) / cos φ) with hw | hw
    · -- above the floor point `(q₀, 0) ∈ [D(0), Z^L_K]`
      refine hvert 0 hq1 ?_
      have hDf : Dc 0 1 = 0 := by
        have := hT.D_wall 0 ⟨le_rfl, by linarith⟩
        rwa [zero_add, hK.isCap.supportFn_pi_div_two, sub_self, inner_u_pi_div_two] at this
      refine hC.segment_subset (hDC _ ⟨le_rfl, by linarith⟩) hZC ?_
      refine mem_segment_of_line' (n := u (π / 2)) (by simp) ?_ ?_ ?_ ?_
      · rw [inner_u_pi_div_two, inner_u_pi_div_two, hDf, vec_coord_one]
      · rw [inner_u_pi_div_two, inner_u_pi_div_two, ptZL_coord_one, vec_coord_one]
      · rw [vec_coord_zero]; exact hx1
      · rw [ptZL_coord_zero, vec_coord_zero]; exact hw
    · -- above the point of `d^L_K` below `q`, which lies in `[Z^L_K, x^L_K]`
      have hw' : 1 - supportFn K (π - φ) < q 0 * cos φ := (div_lt_iff₀ hc).1 hw
      set y := (supportFn K (π - φ) - 1 + q 0 * cos φ) / sin φ with hy_def
      have hyr : y * sin φ = supportFn K (π - φ) - 1 + q 0 * cos φ := by
        rw [hy_def]; field_simp
      have hxL := inner_innerCorner_u_add K (π / 2 - φ)
      rw [show π / 2 - φ + π / 2 = π - φ by ring, inner_u_decomp, cos_pi_sub, sin_pi_sub] at hxL
      rw [hT.D_end] at hx2
      have e1 := mul_le_mul_of_nonneg_right hx2 hc.le
      refine hvert y (le_of_mul_le_mul_right (by linarith) hs) ?_
      refine hC.segment_subset hZC (hDC _ ⟨by linarith, le_rfl⟩) ?_
      rw [hT.D_end]
      refine mem_segment_of_line (n := u (π - φ))
        (by rw [u_coord_zero, cos_pi_sub, neg_ne_zero]; exact hc.ne') ?_ ?_ ?_ ?_
      · rw [inner_u_decomp, inner_u_decomp, cos_pi_sub, sin_pi_sub, ptZL_coord_zero,
          ptZL_coord_one, vec_coord_zero, vec_coord_one]
        have : (1 - supportFn K (π - φ)) / cos φ * cos φ = 1 - supportFn K (π - φ) :=
          div_mul_cancel₀ _ hc.ne'
        linarith
      · rw [inner_u_decomp, inner_u_decomp, cos_pi_sub, sin_pi_sub, vec_coord_zero,
          vec_coord_one]
        linarith
      · rw [ptZL_coord_one, vec_coord_one, hy_def]
        exact div_nonneg (by linarith) hs.le
      · rw [vec_coord_one]
        exact le_of_mul_le_mul_right (by linarith) hs
  · -- below the core: impossible, `x_K(t) ∉ int H̆^L_K`
    exfalso
    have h3 := hK.inner_innerCorner_u_le_left hφ0 (by linarith) (by linarith [ht.1]) ht.2
    rw [inner_u_decomp, cos_pi_sub, sin_pi_sub, hx] at h3
    have e2 := mul_lt_mul_of_pos_right hy hs
    linarith
  · -- below `B`: impossible, `B` lies below and right of `x^R_K ∉ int H̆^L_K`
    exfalso
    have h1 : Bc (π / 2 - θ) 0 ≤ Bc t 0 := hT.B_x_mono ⟨le_rfl, by linarith⟩ ht ht.1
    have h2 : Bc t 1 ≤ Bc (π / 2 - θ) 1 := hT.B_y_anti ⟨le_rfl, by linarith⟩ ht ht.1
    rw [hT.B_start, hx] at h1
    rw [hT.B_start] at h2
    have h3 := hK.inner_innerCorner_u_le_left hφ0 (t := φ) (by linarith) hφ0.le (by linarith)
    rw [inner_u_decomp, cos_pi_sub, sin_pi_sub] at h3
    have e1 := mul_le_mul_of_nonneg_right h1 hc.le
    have e2 := mul_lt_mul_of_pos_right (lt_of_lt_of_le hy h2) hs
    linarith

/-- **(c)** `N(K) \ H̆^R_K \ H̆^L_K ⊆ Ω ∪ {η = 0}`, where `Ω = {Z^L < ξ < W^R, 0 < η < U(ξ)}` is the
region under the roof `U = d | c | b` of Lemma 8.2.3. -/
theorem GerverNiche.niche_diff_subset (hG : GerverNiche φ θ K Bc Dc) :
    (niche K (π / 2) \ hpGe φ (supportFn K φ - 1)) \ hpGe (π - φ) (supportFn K (π - φ) - 1)
      ⊆ {q : ℝ² | q 0 ∈ Ioo ((1 - supportFn K (π - φ)) / cos φ) ((supportFn K φ - 1) / cos φ)
          ∧ 0 < q 1 ∧ q 1 < coreU φ K (q 0)} ∪ {q : ℝ² | q 1 = 0} := by
  have hT := hG.toGerverTails
  have hpi := pi_gt_three
  have hφ0 := hT.phi_pos
  have hφ1 : φ < π / 4 := by linarith [hT.phi_le]
  have hφθ := hT.phi_lt_theta
  have hθ := hT.theta_lt
  have hK := hT.injective
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  rintro q ⟨⟨hqN, hqR⟩, hqL⟩
  have hR : q 0 * cos φ + q 1 * sin φ < supportFn K φ - 1 := by
    have h : ¬ (supportFn K φ - 1 ≤ ⟪q, u φ⟫) := hqR
    rw [inner_u_decomp, not_le] at h; exact h
  have hL : -(q 0 * cos φ) + q 1 * sin φ < supportFn K (π - φ) - 1 := by
    have h : ¬ (supportFn K (π - φ) - 1 ≤ ⟪q, u (π - φ)⟫) := hqL
    rw [inner_u_decomp, cos_pi_sub, sin_pi_sub, not_le] at h; linarith
  have hq1 : 0 ≤ q 1 := (mem_niche_iff.1 hqN).1.1
  rcases eq_or_lt_of_le hq1 with h0 | h0
  · exact Or.inr h0.symm
  left
  have hqs := mul_pos h0 hs
  refine ⟨⟨(div_lt_iff₀ hc).2 (by linarith), (lt_div_iff₀ hc).2 (by linarith)⟩, h0, ?_⟩
  obtain ⟨hanti, -, -, -⟩ := hK.core_graph hφ0 hφ1
  by_cases h1 : q 0 ≤ coreX K (π / 2 - φ)
  · rw [coreU, coreRoof_of_le h1, coreD, lt_div_iff₀ hs]; linarith
  by_cases h2 : q 0 < coreX K φ
  swap
  · rw [coreU, coreRoof_of_ge (hK.coreX_lt hφ0 hφ1) (not_lt.1 h2), coreB, lt_div_iff₀ hs]
    linarith
  rw [coreU, coreRoof_of_mem (not_le.1 h1) h2]
  obtain ⟨t, ht, hXt, hct⟩ := hK.coreC_of_mem hφ0 hφ1 ⟨(not_le.1 h1).le, h2.le⟩
  rw [hct]
  rcases hG.below q hqN with ⟨s, hs', hx, hy⟩ | ⟨s, hs', hx, hy⟩ | ⟨s, hs', hx, hy⟩
  · -- `D` lies left of `x^L_K`
    exfalso
    have h3 : Dc s 0 ≤ Dc θ 0 := hT.D_x_mono hs' ⟨by linarith, le_rfl⟩ hs'.2
    rw [hT.D_end, hx] at h3
    have e : coreX K (π / 2 - φ) = innerCorner K (π / 2 - φ) 0 := inner_u_zero _
    linarith
  · -- the same point of the core
    have hst : s = t := hanti.injOn hs' ht (by
      show coreX K s = coreX K t
      rw [hXt, coreX, inner_u_zero, hx])
    subst hst
    rw [coreY, inner_u_pi_div_two]; exact hy
  · -- `B` lies right of `x^R_K`
    exfalso
    have h3 : Bc (π / 2 - θ) 0 ≤ Bc s 0 := hT.B_x_mono ⟨le_rfl, by linarith⟩ hs' hs'.1
    rw [hT.B_start, hx] at h3
    have e : coreX K φ = innerCorner K φ 0 := inner_u_zero _
    linarith

/-! ## The three areas -/

/-- The tangent-cap formula for `B_K`: `|conv(B_K ∪ {W^R_K}) \ B_K| = J(X_B, W^R_K) − J(b_B)`. -/
theorem IsInjectiveCap.volumeReal_convexHull_diff_Bset (hK : IsInjectiveCap K) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) (hwid : 1 ≤ (supportFn K 0 + supportFn K π) * cos φ)
    (hN : niche K (π / 2) ⊆ K) :
    volume.real (convexHull ℝ (insert (ptWR φ K) (Bset φ K)) \ Bset φ K)
      = segJ (vtxP (Bset φ K) (π + φ)) (ptWR φ K) - convJ (Bset φ K) (π + φ) (3 * π / 2) := by
  have hcap := hK.isCap
  have hKc := hcap.isCompact
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hφ1⟩
  have hWR := hcap.ptWR_mem hφ0 hφ1 hwid
  set B := Bset φ K with hBdef
  have hBc : IsCompact B := isCompact_Bset hKc
  have hBconv : Convex ℝ B := convex_Bset hcap.convex
  have hBne : B.Nonempty := hcap.Bset_nonempty hφ0.le
  have hB3 := hcap.supportFn_Bset_three_pi_div_two (φ := φ) hφ0.le
  have hBφ := hK.supportFn_Bset_phi hφ0 hφ1 hWR hN
  have hW := vtx2_eq_ptWR (K := K) hc hBφ hB3
  have hT := volumeReal_convexHull_insert_vtx2 hBc hBconv hBne (a := π + φ) (b := 3 * π / 2)
    (by linarith) (by linarith)
  rw [hW] at hT
  have u3 : ∀ q : ℝ², ⟪q, u (3 * π / 2)⟫ = -⟪q, u (π / 2)⟫ := fun q => by
    rw [show 3 * π / 2 = π / 2 + π by ring, u_add_pi, inner_neg_right]
  have hWB : ⟪vtxM B (3 * π / 2), u (π / 2)⟫ = 0 := by
    have h := inner_vtxM_u B (3 * π / 2)
    rw [hB3, u3] at h
    linarith
  have hzero : segJ (ptWR φ K) (vtxM B (3 * π / 2)) = 0 :=
    segJ_eq_zero_of_line_zero (inner_ptWR_u_pi_div_two φ K) hWB
  have hCc := isCompact_convexHull_insert hBc hBconv hBne (ptWR φ K)
  have hdiff := measureReal_sdiff (μ := volume) ((subset_insert _ _).trans (subset_convexHull ℝ _))
    hBc.isClosed.measurableSet hCc.measure_lt_top.ne
  rw [hdiff, hT, hzero]; ring

/-- The tangent-cap formula for `D_K`: `|conv(D_K ∪ {Z^L_K}) \ D_K| = J(Z^L_K, Y_D) − J(d_D)`. -/
theorem IsInjectiveCap.volumeReal_convexHull_diff_Dset (hK : IsInjectiveCap K) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) (hwid : 1 ≤ (supportFn K 0 + supportFn K π) * cos φ)
    (hN : niche K (π / 2) ⊆ K) :
    volume.real (convexHull ℝ (insert (ptZL φ K) (Dset φ K)) \ Dset φ K)
      = segJ (ptZL φ K) (vtxM (Dset φ K) (2 * π - φ))
        - convJ (Dset φ K) (3 * π / 2) (2 * π - φ) := by
  have hcap := hK.isCap
  have hKc := hcap.isCompact
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hφ1⟩
  have hZL := hcap.ptZL_mem hφ0 hφ1 hwid
  set D := Dset φ K with hDdef
  have hDc : IsCompact D := isCompact_Dset hKc
  have hDconv : Convex ℝ D := convex_Dset hcap.convex
  have hDne : D.Nonempty := hcap.Dset_nonempty hφ0.le
  have hD3 := hcap.supportFn_Dset_three_pi_div_two (φ := φ) hφ0.le
  have hDφ := hK.supportFn_Dset_phi hφ0 hφ1 hZL hN
  have hZ := vtx2_eq_ptZL (K := K) hc hDφ hD3
  have hT := volumeReal_convexHull_insert_vtx2 hDc hDconv hDne (a := 3 * π / 2) (b := 2 * π - φ)
    (by linarith) (by linarith)
  rw [hZ] at hT
  have u3 : ∀ q : ℝ², ⟪q, u (3 * π / 2)⟫ = -⟪q, u (π / 2)⟫ := fun q => by
    rw [show 3 * π / 2 = π / 2 + π by ring, u_add_pi, inner_neg_right]
  have hZD : ⟪vtxP D (3 * π / 2), u (π / 2)⟫ = 0 := by
    have h := inner_vtxP_u D (3 * π / 2)
    rw [hD3, u3] at h
    linarith
  have hzero : segJ (vtxP D (3 * π / 2)) (ptZL φ K) = 0 :=
    segJ_eq_zero_of_line_zero hZD (inner_ptZL_u_pi_div_two φ K)
  have hCc := isCompact_convexHull_insert hDc hDconv hDne (ptZL φ K)
  have hdiff := measureReal_sdiff (μ := volume) ((subset_insert _ _).trans (subset_convexHull ℝ _))
    hDc.isClosed.measurableSet hCc.measure_lt_top.ne
  rw [hdiff, hT, hzero]; ring

/-- **The one-dimensional identity**: if `Z ≤ ξ_L < ξ_R ≤ W` and the roof is nonnegative on
`(Z, W)`, then `∫_Z^W U⁺ = ∫_Z^{ξ_L} d + ∫_{ξ_L}^{ξ_R} c + ∫_{ξ_R}^W b` (the equality case of
`integral_pieces_le`). -/
theorem integral_pieces_eq {d c b : ℝ → ℝ} {Z W ξL ξR : ℝ} (hLR : ξL < ξR) (hZL : Z ≤ ξL)
    (hRW : ξR ≤ W) (hd : Continuous d) (hb : Continuous b) (hc : IntegrableOn c (Icc ξL ξR))
    (hpos : ∀ ξ ∈ Ioo Z W, 0 ≤ coreRoof d c b ξL ξR ξ) :
    ∫ ξ in Ioo Z W, max (coreRoof d c b ξL ξR ξ) 0
      = (∫ ξ in Z..ξL, d ξ) + (∫ ξ in ξL..ξR, c ξ) + (∫ ξ in ξR..W, b ξ) := by
  have hUi : ∀ p q, IntervalIntegrable (coreRoof d c b ξL ξR) volume p q := fun p q =>
    (integrableOn_coreRoof hLR hd hb hc (p ⊓ q) (p ⊔ q)).intervalIntegrable
  have hA : ∫ ξ in ξL..ξR, c ξ = ∫ ξ in ξL..ξR, coreRoof d c b ξL ξR ξ := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(countable_singleton ξR).ae_notMem volume] with ξ hξ hmem
    rw [uIoc_of_le hLR.le] at hmem
    rw [coreRoof_of_mem hmem.1 (lt_of_le_of_ne hmem.2 (by simpa using hξ))]
  have hB : ∫ ξ in Z..ξL, d ξ = ∫ ξ in Z..ξL, coreRoof d c b ξL ξR ξ := by
    refine intervalIntegral.integral_congr fun ξ hξ => ?_
    rw [uIcc_of_le hZL] at hξ
    rw [coreRoof_of_le hξ.2]
  have hC : ∫ ξ in ξR..W, b ξ = ∫ ξ in ξR..W, coreRoof d c b ξL ξR ξ := by
    refine intervalIntegral.integral_congr fun ξ hξ => ?_
    rw [uIcc_of_le hRW] at hξ
    rw [coreRoof_of_ge hLR hξ.1]
  have hD : (∫ ξ in Z..ξL, coreRoof d c b ξL ξR ξ) + (∫ ξ in ξL..ξR, coreRoof d c b ξL ξR ξ)
      + (∫ ξ in ξR..W, coreRoof d c b ξL ξR ξ) = ∫ ξ in Z..W, coreRoof d c b ξL ξR ξ := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hUi Z ξL) (hUi ξL ξR),
      intervalIntegral.integral_add_adjacent_intervals (hUi Z ξR) (hUi ξR W)]
  have hE : ∫ ξ in Ioo Z W, max (coreRoof d c b ξL ξR ξ) 0
      = ∫ ξ in Ioo Z W, coreRoof d c b ξL ξR ξ :=
    setIntegral_congr_fun measurableSet_Ioo fun ξ hξ => max_eq_left (hpos ξ hξ)
  have hF : ∫ ξ in Z..W, coreRoof d c b ξL ξR ξ = ∫ ξ in Ioo Z W, coreRoof d c b ξL ξR ξ := by
    rw [intervalIntegral.integral_of_le (hZL.trans (hLR.le.trans hRW)),
      integral_Ioc_eq_integral_Ioo]
  rw [hE, ← hF, ← hD, hA, hB, hC]

/-- The floor `{η = 0}` is a null set. -/
lemma volume_floor : volume {q : ℝ² | q 1 = 0} = 0 := by
  let e : ℝ² ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e volume volume :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
      (volume_preserving_finTwoArrow ℝ)
  have hset : {q : ℝ² | q 1 = 0} = e ⁻¹' (univ ×ˢ {0}) := by
    ext q
    have h2 : (e q).2 = q 1 := rfl
    simp only [mem_ofPred_eq, mem_preimage, mem_prod, mem_univ, true_and, mem_singleton_iff, h2]
  rw [hset, he.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_singleton, mul_zero]

/-! ## Theorem 8.4.6 -/

/-- The core ends lie between the floor points, `Z^L_K ≤ ξ_L < ξ_R ≤ W^R_K`, and the roof is
nonnegative on `(Z^L_K, W^R_K)`: both because the core lies on or above the floor. -/
theorem GerverNiche.coreU_nonneg (hG : GerverNiche φ θ K Bc Dc) :
    (1 - supportFn K (π - φ)) / cos φ ≤ coreX K (π / 2 - φ) ∧
    coreX K φ ≤ (supportFn K φ - 1) / cos φ ∧
    ∀ ξ ∈ Ioo ((1 - supportFn K (π - φ)) / cos φ) ((supportFn K φ - 1) / cos φ),
      0 ≤ coreU φ K ξ := by
  have hT := hG.toGerverTails
  have hpi := pi_gt_three
  have hφ0 := hT.phi_pos
  have hφ1 : φ < π / 4 := by linarith [hT.phi_le]
  have hK := hT.injective
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hY : ∀ t ∈ Icc φ (π / 2 - φ), 0 ≤ coreY K t := fun t ht => by
    rw [coreY, inner_u_pi_div_two]
    exact closure_niche_subset_floor K (hG.core_closure t ht)
  have hxL := inner_innerCorner_u_add K (π / 2 - φ)
  rw [show π / 2 - φ + π / 2 = π - φ by ring, inner_innerCorner_eq_coords, cos_pi_sub,
    sin_pi_sub] at hxL
  have hxR := inner_innerCorner_u (S := K) φ
  rw [inner_innerCorner_eq_coords] at hxR
  have hYL := mul_nonneg (hY (π / 2 - φ) ⟨by linarith, le_rfl⟩) hs.le
  have hYR := mul_nonneg (hY φ ⟨le_rfl, by linarith⟩) hs.le
  refine ⟨(div_le_iff₀ hc).2 (by linarith), (le_div_iff₀ hc).2 (by linarith), fun ξ hξ => ?_⟩
  by_cases h1 : ξ ≤ coreX K (π / 2 - φ)
  · rw [coreU, coreRoof_of_le h1, coreD]
    have := (div_lt_iff₀ hc).1 hξ.1
    exact div_nonneg (by linarith) hs.le
  by_cases h2 : ξ < coreX K φ
  · rw [coreU, coreRoof_of_mem (not_le.1 h1) h2]
    obtain ⟨t, ht, -, hct⟩ := hK.coreC_of_mem hφ0 hφ1 ⟨(not_le.1 h1).le, h2.le⟩
    rw [hct]; exact hY t ht
  · rw [coreU, coreRoof_of_ge (hK.coreX_lt hφ0 hφ1) (not_lt.1 h2), coreB]
    have := (lt_div_iff₀ hc).1 hξ.2
    exact div_nonneg (by linarith) hs.le

/-- **Baek Theorem 8.4.6, the area bound** (without Green's theorem):
`|N(K)| ≤ J(x_K|[φ, π/2 − φ]) − J(b_{B_K}) − J(d_{D_K})` for the cap of Gerver's sofa. -/
theorem GerverNiche.volumeReal_niche_le (hG : GerverNiche φ θ K Bc Dc) :
    volume.real (niche K (π / 2))
      ≤ curveJ (innerCorner K) φ (π / 2 - φ) - convJ (Bset φ K) (π + φ) (3 * π / 2)
        - convJ (Dset φ K) (3 * π / 2) (2 * π - φ) := by
  have hT := hG.toGerverTails
  have hpi := pi_gt_three
  have hφ0 := hT.phi_pos
  have hφ1 : φ < π / 4 := by linarith [hT.phi_le]
  have hφ2 : φ < π / 2 := by linarith
  have hφθ := hT.phi_lt_theta
  have hθ := hT.theta_lt
  have hK := hT.injective
  have hcap := hK.isCap
  have hKc := hcap.isCompact
  have hN := hT.niche_subset
  have hwid2 := width_of_area (hT.area.trans hcap.volumeReal_le_width) hφ0 hT.phi_le
  have hwid : 1 ≤ (supportFn K 0 + supportFn K π) * cos φ := by
    have := sin_pos_of_pos_of_lt_pi hφ0 (by linarith); nlinarith
  -- the ends of the tails (Thm 8.4.3 (2))
  obtain ⟨-, -, -, hXB, -⟩ := hcap.gerver_B_side hφ0 hφθ hθ hT.B_cont hT.B_mem hT.B_wall
    hT.B_start
  obtain ⟨-, -, -, hYD, -⟩ := hcap.gerver_D_side hφ0 hφθ hθ hT.D_cont hT.D_mem hT.D_wall
    hT.D_end
  set N := niche K (π / 2) with hNdef
  set R := hpGe φ (supportFn K φ - 1) with hRdef
  set L := hpGe (π - φ) (supportFn K (π - φ) - 1) with hLdef
  -- `N ⊆ (N ∩ R) ∪ (N ∩ L) ∪ (N \ R \ L)`
  have hsplit : N ⊆ (N ∩ R) ∪ (N ∩ L) ∪ ((N \ R) \ L) := by
    intro q hq
    by_cases hR : q ∈ R
    · exact Or.inl (Or.inl ⟨hq, hR⟩)
    by_cases hL : q ∈ L
    · exact Or.inl (Or.inr ⟨hq, hL⟩)
    exact Or.inr ⟨⟨hq, hR⟩, hL⟩
  have hfinN : volume N ≠ ⊤ := measure_ne_top_of_subset hN hKc.measure_lt_top.ne
  have h0 : volume.real N
      ≤ volume.real (N ∩ R) + volume.real (N ∩ L) + volume.real ((N \ R) \ L) := by
    have hsub : (N ∩ R) ∪ (N ∩ L) ∪ ((N \ R) \ L) ⊆ N :=
      union_subset (union_subset inter_subset_left inter_subset_left)
        (sdiff_subset.trans sdiff_subset)
    have e1 := measureReal_mono hsplit (measure_ne_top_of_subset hsub hfinN)
    have e2 := measureReal_union_le (μ := volume) ((N ∩ R) ∪ (N ∩ L)) ((N \ R) \ L)
    have e3 := measureReal_union_le (μ := volume) (N ∩ R) (N ∩ L)
    linarith
  -- (a)
  have hCB := isCompact_convexHull_insert (isCompact_Bset hKc) (convex_Bset hcap.convex)
    (hcap.Bset_nonempty hφ0.le) (ptWR φ K)
  have h1 : volume.real (N ∩ R) ≤ segJ (vtxP (Bset φ K) (π + φ)) (ptWR φ K)
      - convJ (Bset φ K) (π + φ) (3 * π / 2) := by
    rw [← hK.volumeReal_convexHull_diff_Bset hφ0 hφ2 hwid hN]
    exact measureReal_mono hG.niche_inter_right_subset
      (measure_ne_top_of_subset sdiff_subset hCB.measure_lt_top.ne)
  -- (b)
  have hCD := isCompact_convexHull_insert (isCompact_Dset hKc) (convex_Dset hcap.convex)
    (hcap.Dset_nonempty hφ0.le) (ptZL φ K)
  have h2 : volume.real (N ∩ L) ≤ segJ (ptZL φ K) (vtxM (Dset φ K) (2 * π - φ))
      - convJ (Dset φ K) (3 * π / 2) (2 * π - φ) := by
    rw [← hK.volumeReal_convexHull_diff_Dset hφ0 hφ2 hwid hN]
    exact measureReal_mono hG.niche_inter_left_subset
      (measure_ne_top_of_subset sdiff_subset hCD.measure_lt_top.ne)
  -- (c)
  obtain ⟨hZL, hRW, hUpos⟩ := hG.coreU_nonneg
  obtain ⟨-, -, hcint, -⟩ := hK.core_graph hφ0 hφ1
  have hLR := hK.coreX_lt hφ0 hφ1
  have hUint : IntegrableOn (coreU φ K)
      (Ioo ((1 - supportFn K (π - φ)) / cos φ) ((supportFn K φ - 1) / cos φ)) :=
    (integrableOn_coreRoof hLR (continuous_coreD φ K) (continuous_coreB φ K) hcint _ _).mono_set
      Ioo_subset_Icc_self
  have hvol := volume_underGraph hUint
  have hpieces : ∫ ξ in Ioo ((1 - supportFn K (π - φ)) / cos φ) ((supportFn K φ - 1) / cos φ),
        max (coreU φ K ξ) 0
      = (∫ ξ in (1 - supportFn K (π - φ)) / cos φ..coreX K (π / 2 - φ), coreD φ K ξ)
        + (∫ ξ in coreX K (π / 2 - φ)..coreX K φ, coreC φ K ξ)
        + (∫ ξ in coreX K φ..(supportFn K φ - 1) / cos φ, coreB φ K ξ) :=
    integral_pieces_eq hLR hZL hRW (continuous_coreD φ K) (continuous_coreB φ K) hcint hUpos
  have hJ := hK.core_J_eq hφ0 hφ1
  have hle : volume ((N \ R) \ L) ≤ ENNReal.ofReal (∫ ξ in Ioo ((1 - supportFn K (π - φ)) / cos φ)
      ((supportFn K φ - 1) / cos φ), max (coreU φ K ξ) 0) := by
    refine (measure_mono hG.niche_diff_subset).trans ((measure_union_le _ _).trans ?_)
    rw [volume_floor, add_zero, hvol]
  have h3 : volume.real ((N \ R) \ L) ≤ ∫ ξ in Ioo ((1 - supportFn K (π - φ)) / cos φ)
      ((supportFn K φ - 1) / cos φ), max (coreU φ K ξ) 0 :=
    ENNReal.toReal_le_of_le_ofReal (integral_nonneg fun ξ => le_max_right _ _) hle
  -- the segment terms cancel: `X_B = x^R_K`, `Y_D = x^L_K`
  have eR : segJ (vtxP (Bset φ K) (π + φ)) (ptWR φ K) + segJ (ptWR φ K) (innerCorner K φ) = 0 := by
    rw [hXB, segJ_comm (ptWR φ K)]; ring
  have eL : segJ (innerCorner K (π / 2 - φ)) (ptZL φ K)
      + segJ (ptZL φ K) (vtxM (Dset φ K) (2 * π - φ)) = 0 := by
    rw [hYD, segJ_comm (ptZL φ K)]; ring
  linarith

/-- **Baek Theorem 8.4.6**: `𝒬(K, B_K, D_K) ≤ A(K)` for the cap `K` of Gerver's sofa. -/
theorem GerverNiche.Qfun_le_sofaArea (hG : GerverNiche φ θ K Bc Dc) :
    Qfun φ K (Bset φ K) (Dset φ K) ≤ sofaArea K (π / 2) := by
  have hT := hG.toGerverTails
  have hcap := hT.injective.isCap
  obtain ⟨-, -, -, hXB, -⟩ := hcap.gerver_B_side hT.phi_pos hT.phi_lt_theta hT.theta_lt
    hT.B_cont hT.B_mem hT.B_wall hT.B_start
  obtain ⟨-, -, -, hYD, -⟩ := hcap.gerver_D_side hT.phi_pos hT.phi_lt_theta hT.theta_lt
    hT.D_cont hT.D_mem hT.D_wall hT.D_end
  have h := hG.volumeReal_niche_le
  rw [sofaArea, Qfun, hXB, hYD, segJ_self, segJ_self, ← measureReal_def, ← measureReal_def]
  linarith

/-- **Baek Theorem 8.4.6 with Theorem 8.2.4**: `𝒬(K, B_K, D_K) = A(K)` for the cap of Gerver's
sofa. -/
theorem GerverNiche.sofaArea_eq_Qfun (hG : GerverNiche φ θ K Bc Dc) :
    sofaArea K (π / 2) = Qfun φ K (Bset φ K) (Dset φ K) := by
  have hT := hG.toGerverTails
  have hpi := pi_gt_three
  have hK := hT.injective
  have hwid2 := width_of_area (hT.area.trans hK.isCap.volumeReal_le_width) hT.phi_pos hT.phi_le
  exact le_antisymm
    (hK.sofaArea_le_Qfun hT.phi_pos (by linarith [hT.phi_le]) hwid2 hT.niche_subset)
    hG.Qfun_le_sofaArea

end Sofa
