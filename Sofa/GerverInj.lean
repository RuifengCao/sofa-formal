/-
# Sofa/GerverInj.lean — Theorem 6.1.2 for Gerver's sofa: `C(G)` satisfies the injectivity condition

Baek proves Theorem 6.1.2 in one line by citing Gerver's paper (Theorem 2 of [Ger92]: `G` is a
balanced maximum sofa).  Here it is verified directly for the cap `K = C(G)` of the upstream sofa
(`isInjectiveCap_Kg`), from the explicit support function `h_K = p₁ + 1` on `[0, π/2]`,
`h_K(· + π/2) = p₂ + 1` (`Sofa/GerverCap.lean`):

* `p₁`, `p₂` are `C¹` (`hasDerivAt_p₁'`, `hasDerivAt_p₂'`): they are differentiable off the four
  break points with continuous derivatives `p₁'`, `p₂'` (`Sofa/GerverRomik.lean`), so by the
  fundamental theorem of calculus with countably many exceptions they are the integrals of `p₁'`,
  `p₂'`;
* hence the edges of `K` in the directions `(0, π/2)` and `(π/2, π)` are single points, and
  `edgeMax`, `edgeMin` are `p₁'`, `p₂'` there (right and left derivatives of `h_K`); in the
  directions `0` and `π` the edges are the corners `(1, 0)`, `(4x₀ − 3, 0)`;
* `p₁'`, `p₂'` are Lipschitz (their derivatives `r(π/2 − t) − p₁ − 1`, `r − p₂ − 1` are bounded),
  so `arcFn K` is Lipschitz on `[0, c]` (`c < π/2`) and on `[π/2, π]`, and `σ_K` is absolutely
  continuous on `[0, π/2)` and `(π/2, π]` (`sigmaK_restrict_ac`);
* the arm functions are `f_K = F + 1`, `g_K = F(π/2 − ·) + 1` with Romik's `F = p₂ − p₁'`
  (continuous), and `F > 0` on `(0, π/2)`: `F = A + t − φ` on `[φ, π/2 − θ]`, `F = r` on
  `[π/2 − θ, π/2 − φ]` (`Sofa/GerverRomik.lean`), and on the two end pieces
  `F = (3 − 3x₀) sin t − (1 − cos t)/2` resp. `F = (3 − 3x₀) sin t − cos t/2 − 1`.

STATUS: [PROOF-C] [AXIOM-CHECK] round 40 (2026-09-23, Opus 5.5), no `sorry`.
-/
import Sofa.GerverRomik

noncomputable section

open Real Set MeasureTheory intervalIntegral MovingSofa Filter Topology
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa.GP

open GC IA
open MovingSofa.GerversSofa (A B φ θ r)

/-! ## `p₁`, `p₂` are `C¹` -/

/-- The four break points. -/
def brkSet : Set ℝ := {φ, θ, π / 2 - θ, π / 2 - φ}

lemma brkSet_countable : brkSet.Countable := by
  simp only [brkSet, countable_insert, countable_singleton]

lemma mem_brkSet_reflect {t : ℝ} (ht : π / 2 - t ∈ brkSet) : t ∈ brkSet := by
  simp only [brkSet, mem_insert_iff, mem_singleton_iff] at ht ⊢
  rcases ht with h | h | h | h
  · right; right; right; linarith
  · right; right; left; linarith
  · right; left; linarith
  · left; linarith

/-- `r` is continuous away from the break points (on all of `ℝ`). -/
lemma continuousAt_r_of_not_mem {t : ℝ} (ht : t ∉ brkSet) : ContinuousAt r t := by
  simp only [brkSet, mem_insert_iff, mem_singleton_iff, not_or] at ht
  obtain ⟨h1, h2, h3, h4⟩ := ht
  obtain ⟨h01, h12, h23, h34, -⟩ := brk_mono
  rcases lt_or_gt_of_ne h1 with a1 | a1
  · have hev : r =ᶠ[𝓝 t] fun _ => (1 : ℝ) / 2 := by
      filter_upwards [isOpen_Iio.mem_nhds a1] with s hs
      exact r_of_le_φ (le_of_lt hs)
    exact (continuousAt_congr hev).2 continuousAt_const
  rcases lt_or_gt_of_ne h2 with a2 | a2
  · exact continuousAt_r (k := 1) (by norm_num) ⟨a1, a2⟩
  rcases lt_or_gt_of_ne h3 with a3 | a3
  · exact continuousAt_r (k := 2) (by norm_num) ⟨a2, a3⟩
  rcases lt_or_gt_of_ne h4 with a4 | a4
  · exact continuousAt_r (k := 3) (by norm_num) ⟨a3, a4⟩
  · exact continuousAt_r_top a4

lemma continuousAt_r_reflect {t : ℝ} (ht : t ∉ brkSet) : ContinuousAt r (π / 2 - t) :=
  continuousAt_r_of_not_mem fun h => ht (mem_brkSet_reflect h)

/-- `p₁ b − p₁ a = ∫_a^b p₁'`. -/
lemma p₁_sub (a b : ℝ) : p₁ b - p₁ a = ∫ s in a..b, dp₁ s :=
  (integral_eq_of_hasDerivAt_off_countable p₁ dp₁ brkSet_countable
    continuous_p₁.continuousOn (fun _ ht => hasDerivAt_p₁ (continuousAt_r_reflect ht.2))
    (continuous_dp₁.intervalIntegrable _ _)).symm

lemma p₂_sub (a b : ℝ) : p₂ b - p₂ a = ∫ s in a..b, dp₂ s :=
  (integral_eq_of_hasDerivAt_off_countable p₂ dp₂ brkSet_countable
    continuous_p₂.continuousOn (fun _ ht => hasDerivAt_p₂ (continuousAt_r_of_not_mem ht.2))
    (continuous_dp₂.intervalIntegrable _ _)).symm

/-- **`p₁` is `C¹`**: `p₁' = dp₁` everywhere, also at the break points. -/
lemma hasDerivAt_p₁' (t : ℝ) : HasDerivAt p₁ (dp₁ t) t := by
  have e : p₁ = fun s => p₁ 0 + ∫ x in (0 : ℝ)..s, dp₁ x := by
    funext s; rw [← p₁_sub]; ring
  rw [e]
  exact (integral_hasDerivAt_right (continuous_dp₁.intervalIntegrable _ _)
    (continuous_dp₁.stronglyMeasurableAtFilter _ _) continuous_dp₁.continuousAt).const_add _

lemma hasDerivAt_p₂' (t : ℝ) : HasDerivAt p₂ (dp₂ t) t := by
  have e : p₂ = fun s => p₂ 0 + ∫ x in (0 : ℝ)..s, dp₂ x := by
    funext s; rw [← p₂_sub]; ring
  rw [e]
  exact (integral_hasDerivAt_right (continuous_dp₂.intervalIntegrable _ _)
    (continuous_dp₂.stronglyMeasurableAtFilter _ _) continuous_dp₂.continuousAt).const_add _

/-! ## Bounds on `[0, π/2]` -/

lemma intervalIntegrable_r_reflect (a b : ℝ) :
    IntervalIntegrable (fun s => r (π / 2 - s)) volume a b := by
  have := (intervalIntegrable_r (π / 2 - a) (π / 2 - b)).comp_sub_left (π / 2)
  simpa using this

/-- `0 ≤ p₁ + 1 ≤ 2` on `[0, π/2]`. -/
lemma p₁_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) : 0 ≤ p₁ t + 1 ∧ p₁ t + 1 ≤ 2 := by
  rw [p₁_uniform]
  obtain ⟨xa0, xa1⟩ := x_range (reflect_mem ht)
  obtain ⟨ya0, ya1⟩ := y_range (reflect_mem ht)
  obtain ⟨x01, -⟩ := x0_bounds
  obtain ⟨hs, hc⟩ := sin_cos_nonneg ht.1 ht.2
  have k1 := mul_le_of_le_one_left hc xa1
  have k2 := mul_le_of_le_one_left hs ya1
  have k3 := mul_nonneg (show (0 : ℝ) ≤ GerversSofa.x (π / 2 - t) by linarith) hc
  have k4 := mul_nonneg ya0 hs
  have hc1 := cos_le_one t
  have hs1 := sin_le_one t
  constructor <;> nlinarith

/-- `0 ≤ p₂ + 1 ≤ 4` on `[0, π/2]`. -/
lemma p₂_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) : 0 ≤ p₂ t + 1 ∧ p₂ t + 1 ≤ 4 := by
  rw [p₂_uniform]
  obtain ⟨xa0, xa1⟩ := x_range ht
  obtain ⟨ya0, ya1⟩ := y_range ht
  obtain ⟨x01, x02⟩ := x0_bounds
  obtain ⟨hs, hc⟩ := sin_cos_nonneg ht.1 ht.2
  have k1 := mul_le_of_le_one_left hc ya1
  have k2 := mul_nonneg ya0 hc
  have k3 : 0 ≤ (2 + GerversSofa.x t - 4 * GerversSofa.x 0) * sin t :=
    mul_nonneg (by linarith) hs
  have k4 : (2 + GerversSofa.x t - 4 * GerversSofa.x 0) * sin t ≤ 3 :=
    (mul_le_of_le_one_right (by linarith) (sin_le_one t)).trans (by linarith)
  have hc1 := cos_le_one t
  constructor <;> nlinarith

/-- `p₁'` is `5`-Lipschitz on `[0, π/2]`. -/
lemma dp₁_lip {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π / 2) :
    |dp₁ b - dp₁ a| ≤ 5 * (b - a) := by
  have e : dp₁ b - dp₁ a = ∫ s in a..b, (r (π / 2 - s) - p₁ s - 1) :=
    (integral_eq_of_hasDerivAt_off_countable dp₁ _ brkSet_countable
      continuous_dp₁.continuousOn (fun _ ht => hasDerivAt_dp₁ (continuousAt_r_reflect ht.2))
      (((intervalIntegrable_r_reflect a b).sub (continuous_p₁.intervalIntegrable _ _)).sub
        intervalIntegrable_const)).symm
  rw [e]
  have hbound : ∀ s ∈ uIoc a b, ‖r (π / 2 - s) - p₁ s - 1‖ ≤ 5 := by
    intro s hs
    rw [uIoc_of_le hab] at hs
    have hr := r_nonneg_le (π / 2 - s)
    have hp := p₁_bound (t := s) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hr.1, hr.2, hp.1, hp.2]
  have h := norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at h
  exact h

/-- `p₂'` is `5`-Lipschitz on `[0, π/2]`. -/
lemma dp₂_lip {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π / 2) :
    |dp₂ b - dp₂ a| ≤ 5 * (b - a) := by
  have e : dp₂ b - dp₂ a = ∫ s in a..b, (r s - p₂ s - 1) :=
    (integral_eq_of_hasDerivAt_off_countable dp₂ _ brkSet_countable
      continuous_dp₂.continuousOn (fun _ ht => hasDerivAt_dp₂ (continuousAt_r_of_not_mem ht.2))
      (((intervalIntegrable_r a b).sub (continuous_p₂.intervalIntegrable _ _)).sub
        intervalIntegrable_const)).symm
  rw [e]
  have hbound : ∀ s ∈ uIoc a b, ‖r s - p₂ s - 1‖ ≤ 5 := by
    intro s hs
    rw [uIoc_of_le hab] at hs
    have hr := r_nonneg_le s
    have hp := p₂_bound (t := s) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hr.1, hr.2, hp.1, hp.2]
  have h := norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at h
  exact h

/-! ## The edges of `K = C(G)` -/

lemma dp₁_zero : dp₁ 0 = 0 := by
  obtain ⟨p1, -⟩ := bounds
  rw [dp₁, sub_zero, y_of_ge (by linarith), sin_zero, cos_zero]; ring

lemma dp₂_half : dp₂ (π / 2) = 0 := by
  obtain ⟨p1, -⟩ := bounds
  rw [dp₂, y_of_ge (β := π / 2) (by linarith), Real.sin_pi_div_two, Real.cos_pi_div_two]; ring

/-- `edgeMax K t = p₁'(t)` on `[0, π/2)` (the right derivative of `h_K = p₁ + 1`). -/
lemma edgeMax_Kg_of {t : ℝ} (h0 : 0 ≤ t) (h1 : t < π / 2) : edgeMax Kg t = dp₁ t := by
  have hK := isCap_Kg
  have h2 : HasDerivWithinAt (supportFn Kg) (dp₁ t) (Ioi t) t := by
    refine ((hasDerivAt_p₁' t).add_const 1).hasDerivWithinAt.congr_of_eventuallyEq ?_
      (supportFn_Kg ⟨h0, h1.le⟩)
    filter_upwards [Ioo_mem_nhdsGT h1] with s hs
    exact supportFn_Kg ⟨by linarith [hs.1], hs.2.le⟩
  exact (uniqueDiffWithinAt_Ioi t).eq_deriv _
    (hasDerivWithinAt_supportFn_Ioi hK.isCompact hK.nonempty t) h2

/-- `edgeMin K t = p₁'(t)` on `(0, π/2]` (the left derivative of `h_K = p₁ + 1`). -/
lemma edgeMin_Kg_of {t : ℝ} (h0 : 0 < t) (h1 : t ≤ π / 2) : edgeMin Kg t = dp₁ t := by
  have hK := isCap_Kg
  have h2 : HasDerivWithinAt (supportFn Kg) (dp₁ t) (Iio t) t := by
    refine ((hasDerivAt_p₁' t).add_const 1).hasDerivWithinAt.congr_of_eventuallyEq ?_
      (supportFn_Kg ⟨h0.le, h1⟩)
    filter_upwards [Ioo_mem_nhdsLT h0] with s hs
    exact supportFn_Kg ⟨hs.1.le, by linarith [hs.2]⟩
  exact (uniqueDiffWithinAt_Iio t).eq_deriv _
    (hasDerivWithinAt_supportFn_Iio hK.isCompact hK.nonempty t) h2

/-- `edgeMax K (t + π/2) = p₂'(t)` on `[0, π/2)`. -/
lemma edgeMax_Kg_add_of {t : ℝ} (h0 : 0 ≤ t) (h1 : t < π / 2) :
    edgeMax Kg (t + π / 2) = dp₂ t := by
  have hK := isCap_Kg
  have hp : HasDerivAt p₂ (dp₂ t) (t + π / 2 - π / 2) := by
    rw [add_sub_cancel_right]; exact hasDerivAt_p₂' t
  have h2 : HasDerivWithinAt (supportFn Kg) (dp₂ t) (Ioi (t + π / 2)) (t + π / 2) := by
    refine ((hp.comp_sub_const (t + π / 2) (π / 2)).add_const 1).hasDerivWithinAt.congr_of_eventuallyEq
      ?_ (by rw [add_sub_cancel_right]; exact supportFn_Kg' ⟨h0, h1.le⟩)
    filter_upwards [Ioo_mem_nhdsGT (show t + π / 2 < π by linarith)] with s hs
    have := supportFn_Kg' (α := s - π / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rwa [sub_add_cancel] at this
  exact (uniqueDiffWithinAt_Ioi _).eq_deriv _
    (hasDerivWithinAt_supportFn_Ioi hK.isCompact hK.nonempty _) h2

/-- Below the horizontal direction the support function is that of the corner `(1, 0)`. -/
lemma supportFn_Kg_neg {s : ℝ} (hs0 : -(π / 2) ≤ s) (hs1 : s ≤ 0) : supportFn Kg s = cos s := by
  have hK := isCap_Kg
  have hc : 0 ≤ cos s := cos_nonneg_of_mem_Icc ⟨hs0, by linarith [Real.pi_pos]⟩
  have hsn : sin s ≤ 0 := sin_nonpos_of_nonpos_of_neg_pi_le hs1 (by linarith [Real.pi_pos])
  apply le_antisymm
  · rw [supportFn_le_iff hK.isCompact hK.nonempty]
    intro z hz
    rw [Ccap_gerver] at hz
    obtain ⟨⟨hz0, hz1, -⟩, -, -⟩ := mem_Cvx.1 hz
    rw [inner_u_decomp]
    nlinarith [mul_le_mul_of_nonneg_right hz0 hc, mul_nonpos_of_nonneg_of_nonpos hz1 hsn]
  · have hmem : pt 1 0 ∈ Kg := by
      rw [← ptA_zero]; exact gerversSofa_subset_Kg (ptA_mem ⟨le_rfl, by positivity⟩)
    have := le_supportFn hK.isCompact hmem s
    rwa [inner_u_decomp, pt_zero, pt_one, one_mul, zero_mul, add_zero] at this

/-- Beyond the direction `π` the support function is that of the corner `(4x₀ − 3, 0)`. -/
lemma supportFn_Kg_pi {s : ℝ} (hs0 : π ≤ s) (hs1 : s ≤ π + π / 2) :
    supportFn Kg s = (4 * GerversSofa.x 0 - 3) * cos s := by
  have hK := isCap_Kg
  have hc : cos s ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hs1
  have hsn : sin s ≤ 0 := by
    have h := sin_nonneg_of_nonneg_of_le_pi (x := s - π) (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at h; linarith
  apply le_antisymm
  · rw [supportFn_le_iff hK.isCompact hK.nonempty]
    intro z hz
    rw [Ccap_gerver] at hz
    obtain ⟨⟨-, hz1, -⟩, hz3, -⟩ := mem_Cvx.1 hz
    rw [inner_u_decomp]
    nlinarith [mul_le_mul_of_nonpos_right hz3 hc, mul_nonpos_of_nonneg_of_nonpos hz1 hsn]
  · have hmem : pt (4 * GerversSofa.x 0 - 3) 0 ∈ Kg := by
      rw [← ptC_pi_div_two]; exact gerversSofa_subset_Kg (ptC_mem ⟨by positivity, le_rfl⟩)
    have := le_supportFn hK.isCompact hmem s
    rwa [inner_u_decomp, pt_zero, pt_one, zero_mul, add_zero] at this

/-- The edge in the direction `0` is the corner `(1, 0)`: `edgeMin K 0 = 0`. -/
lemma edgeMin_Kg_zero : edgeMin Kg 0 = 0 := by
  have hK := isCap_Kg
  have hpi := Real.pi_pos
  have h2 : HasDerivWithinAt (supportFn Kg) 0 (Iio 0) 0 := by
    have hcos : HasDerivWithinAt cos (-sin 0) (Iio 0) 0 := (hasDerivAt_cos 0).hasDerivWithinAt
    rw [sin_zero, neg_zero] at hcos
    refine hcos.congr_of_eventuallyEq ?_ (supportFn_Kg_neg (by linarith) le_rfl)
    filter_upwards [Ioo_mem_nhdsLT (show -(π / 2) < 0 by linarith)] with s hs
    exact supportFn_Kg_neg hs.1.le hs.2.le
  exact (uniqueDiffWithinAt_Iio 0).eq_deriv _
    (hasDerivWithinAt_supportFn_Iio hK.isCompact hK.nonempty 0) h2

/-- The edge in the direction `π` is the corner `(4x₀ − 3, 0)`: `edgeMax K π = 0`. -/
lemma edgeMax_Kg_pi : edgeMax Kg π = 0 := by
  have hK := isCap_Kg
  have hpi := Real.pi_pos
  have h2 : HasDerivWithinAt (supportFn Kg) 0 (Ioi π) π := by
    have hcos : HasDerivWithinAt (fun s => (4 * GerversSofa.x 0 - 3) * cos s)
        ((4 * GerversSofa.x 0 - 3) * -sin π) (Ioi π) π :=
      ((hasDerivAt_cos π).const_mul _).hasDerivWithinAt
    rw [sin_pi, neg_zero, mul_zero] at hcos
    refine hcos.congr_of_eventuallyEq ?_ (supportFn_Kg_pi le_rfl (by linarith))
    filter_upwards [Ioo_mem_nhdsGT (show π < π + π / 2 by linarith)] with s hs
    exact supportFn_Kg_pi hs.1.le hs.2.le
  exact (uniqueDiffWithinAt_Ioi π).eq_deriv _
    (hasDerivWithinAt_supportFn_Ioi hK.isCompact hK.nonempty π) h2

/-- `edgeMax K (t + π/2) = p₂'(t)` on `[0, π/2]`. -/
lemma edgeMax_Kg_add_of' {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ π / 2) :
    edgeMax Kg (t + π / 2) = dp₂ t := by
  rcases h1.lt_or_eq with h | h
  · exact edgeMax_Kg_add_of h0 h
  · subst h
    rw [show π / 2 + π / 2 = π by ring, edgeMax_Kg_pi, dp₂_half]

/-! ## `σ_K` is absolutely continuous -/

lemma supportFn_Kg_le {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (π / 2)) : supportFn Kg s ≤ 2 := by
  rw [supportFn_Kg hs]; exact (p₁_bound hs).2

lemma supportFn_Kg_le' {s : ℝ} (hs : s ∈ Icc (π / 2) π) : supportFn Kg s ≤ 4 := by
  have h := supportFn_Kg' (α := s - π / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩
  rw [sub_add_cancel] at h
  rw [h]; exact (p₂_bound ⟨by linarith [hs.1], by linarith [hs.2]⟩).2

lemma integral_supportFn_Kg_le {a b C : ℝ} (hab : a ≤ b) (h : ∀ s ∈ Icc a b, supportFn Kg s ≤ C) :
    ∫ s in a..b, supportFn Kg s ≤ C * (b - a) := by
  have hK := isCap_Kg
  have := intervalIntegral.integral_mono_on hab (integrable_supportFn hK.isCompact hK.nonempty a b)
    (intervalIntegrable_const (c := C)) h
  rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at this

lemma arcFn_Kg_sub {a b : ℝ} :
    arcFn Kg b - arcFn Kg a = edgeMax Kg b - edgeMax Kg a + ∫ s in a..b, supportFn Kg s := by
  have hK := isCap_Kg
  rw [arcFn, arcFn, inner_vtxP_v, inner_vtxP_v, ← integral_interval_sub_left
    (integrable_supportFn hK.isCompact hK.nonempty 0 b)
    (integrable_supportFn hK.isCompact hK.nonempty 0 a)]
  ring

lemma arcFn_Kg_lip_left {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < π / 2) :
    arcFn Kg b - arcFn Kg a ≤ 7 * (b - a) := by
  rw [arcFn_Kg_sub, edgeMax_Kg_of (ha.trans hab) hb, edgeMax_Kg_of ha (hab.trans_lt hb)]
  have h1 := integral_supportFn_Kg_le hab fun s hs =>
    supportFn_Kg_le ⟨ha.trans hs.1, hs.2.trans hb.le⟩
  have h2 := dp₁_lip ha hab hb.le
  rw [abs_le] at h2
  linarith

lemma arcFn_Kg_lip_right {a b : ℝ} (ha : π / 2 ≤ a) (hab : a ≤ b) (hb : b ≤ π) :
    arcFn Kg b - arcFn Kg a ≤ 9 * (b - a) := by
  have ea := edgeMax_Kg_add_of' (t := a - π / 2) (by linarith) (by linarith)
  have eb := edgeMax_Kg_add_of' (t := b - π / 2) (by linarith) (by linarith)
  rw [sub_add_cancel] at ea eb
  rw [arcFn_Kg_sub, ea, eb]
  have h1 := integral_supportFn_Kg_le hab fun s hs =>
    supportFn_Kg_le' ⟨ha.trans hs.1, hs.2.trans hb⟩
  have h2 := dp₂_lip (a := a - π / 2) (b := b - π / 2) (by linarith) (by linarith) (by linarith)
  rw [abs_le] at h2
  linarith

lemma edgeLength_Kg_zero : edgeLength Kg 0 = 0 := by
  rw [edgeLength, edgeMax_Kg_of le_rfl (by positivity), edgeMin_Kg_zero, dp₁_zero, sub_zero]

/-- **Def 6.1.2 (1), left half, for `C(G)`**. -/
theorem sigmaK_Kg_ac_left : (sigmaK Kg).restrict (Ico 0 (π / 2)) ≪ volume := by
  have hK := isCap_Kg
  have hKc := hK.isCompact
  have hKne := hK.nonempty
  have hpi := pi_pos
  set c : ℕ → ℝ := fun n => π / 2 - 1 / (n + 1) with hc
  intro s hs
  rw [Measure.restrict_apply' measurableSet_Ico]
  have hzero : sigmaK Kg {(0 : ℝ)} = 0 := by
    rw [sigmaK_singleton hKc hKne, edgeLength_Kg_zero, ENNReal.ofReal_zero]
  have hcover : s ∩ Ico 0 (π / 2) ⊆ {(0 : ℝ)} ∪ ⋃ n : ℕ, (s ∩ Ioc 0 (c n)) := by
    rintro x ⟨hxs, hx0, hx2⟩
    rcases eq_or_lt_of_le hx0 with he | hlt
    · exact Or.inl (by simp [← he])
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < π / 2 - x by linarith)
      exact Or.inr (mem_iUnion.2 ⟨n, hxs, hlt, by simp only [hc]; linarith⟩)
  have hterm : ∀ n : ℕ, sigmaK Kg (s ∩ Ioc 0 (c n)) = 0 := by
    intro n
    have hc0 : (0:ℝ) ≤ c n := by
      simp only [hc]
      have h1 : (1:ℝ) / (n + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [Nat.cast_nonneg (α := ℝ) n]
      linarith [pi_gt_three]
    have hc2 : c n < π / 2 := by
      simp only [hc]
      have : (0:ℝ) < 1 / (n + 1) := by positivity
      linarith
    have hac := sigmaK_restrict_ac hKc hKne hc0 (by norm_num : (0 : ℝ) ≤ 7)
      (fun a b ha hab hbc => arcFn_Kg_lip_left ha hab (lt_of_le_of_lt hbc hc2)) hs
    rwa [Measure.restrict_apply' measurableSet_Ioc] at hac
  refine le_antisymm ?_ bot_le
  calc sigmaK Kg (s ∩ Ico 0 (π / 2))
      ≤ sigmaK Kg ({(0:ℝ)} ∪ ⋃ n : ℕ, (s ∩ Ioc 0 (c n))) := measure_mono hcover
    _ ≤ sigmaK Kg {(0:ℝ)} + sigmaK Kg (⋃ n : ℕ, (s ∩ Ioc 0 (c n))) := measure_union_le _ _
    _ ≤ 0 + ∑' n : ℕ, sigmaK Kg (s ∩ Ioc 0 (c n)) := by
        rw [hzero]; exact add_le_add le_rfl (measure_iUnion_le _)
    _ = 0 := by simp [hterm]

/-- **Def 6.1.2 (1), right half, for `C(G)`**. -/
theorem sigmaK_Kg_ac_right : (sigmaK Kg).restrict (Ioc (π / 2) π) ≪ volume := by
  have hK := isCap_Kg
  have hpi := pi_pos
  exact sigmaK_restrict_ac hK.isCompact hK.nonempty (by linarith) (by norm_num : (0 : ℝ) ≤ 9)
    fun a b ha hab hb => arcFn_Kg_lip_right ha hab hb

/-! ## The arm functions -/

lemma armFm_Kg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) : armFm Kg t = p₂ t + 1 - dp₁ t := by
  rw [armFm_eq, supportFn_Kg' ht]
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst h; rw [edgeMin_Kg_zero, dp₁_zero]
  · rw [edgeMin_Kg_of h ht.2]

lemma armGp_Kg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) : armGp Kg t = p₁ t + 1 + dp₂ t := by
  rw [armGp_eq_add, supportFn_Kg ht, edgeMax_Kg_add_of' ht.1 ht.2]

lemma armFp_Kg {t : ℝ} (h0 : 0 ≤ t) (h1 : t < π / 2) : armFp Kg t = p₂ t + 1 - dp₁ t := by
  rw [armFp_eq, supportFn_Kg' ⟨h0, h1.le⟩, edgeMax_Kg_of h0 h1]

/-! ## `F > 0` -/

lemma x_piece0 {s : ℝ} (hs : s ∈ Icc (0 : ℝ) φ) :
    GerversSofa.x s = GerversSofa.x 0 + sin s / 2 := by
  have e := x_sub s 0
  have hi : ∫ t in (0 : ℝ)..s, r t * cos t = ∫ t in (0 : ℝ)..s, 1 / 2 * cos t := by
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le hs.1] at ht
    simp only [r_of_le_φ (ht.2.trans hs.2)]
  rw [hi, intervalIntegral.integral_const_mul, integral_cos, sin_zero] at e
  linarith

lemma y_piece0 {s : ℝ} (hs : s ∈ Icc (0 : ℝ) φ) : GerversSofa.y s = (1 + cos s) / 2 := by
  have e := y_sub s 0
  have hi : ∫ t in (0 : ℝ)..s, r t * sin t = ∫ t in (0 : ℝ)..s, 1 / 2 * sin t := by
    refine integral_congr fun t ht => ?_
    rw [uIcc_of_le hs.1] at ht
    simp only [r_of_le_φ (ht.2.trans hs.2)]
  rw [hi, intervalIntegral.integral_const_mul, integral_sin, cos_zero, y_zero] at e
  linarith

lemma r_pos_mid {t : ℝ} (h1 : θ < t) (h2 : t ≤ π / 2 - φ) : 0 < r t := by
  obtain ⟨p1, p2, t1, t2, a1, a2, b1, b2⟩ := bounds
  have hpi := Real.pi_gt_d2
  have hpi' := Real.pi_lt_d2
  rw [r_def, if_neg (by linarith), if_neg (by linarith)]
  split_ifs with h3
  · linarith
  · set s := π / 2 - t - φ with hs
    have hs0 : 0 ≤ s := by linarith
    have hs1 : s < θ - φ := by push Not at h3; linarith
    nlinarith [mul_le_mul_of_nonneg_right hs1.le (by linarith : (0 : ℝ) ≤ 1 + A),
      mul_le_mul hs1.le hs1.le hs0 (by linarith : (0 : ℝ) ≤ θ - φ)]

/-- **Romik's `F = p₂ − p₁'` is positive on `(0, π/2)`**: the arms are longer than `1`. -/
theorem F_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) (π / 2)) : 0 < p₂ t - dp₁ t := by
  obtain ⟨p1, p2, t1, t2, a1, a2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  obtain ⟨x01, x02⟩ := x0_bounds
  rcases le_or_gt t φ with h1 | h1
  · -- `F = (3 − 3x₀) sin t − (1 − cos t)/2`
    rw [p₂_sub_dp₁, x_piece0 ⟨ht.1.le, h1⟩, y_piece0 ⟨ht.1.le, h1⟩,
      x_of_ge (β := π / 2 - t) (by linarith), y_of_ge (β := π / 2 - t) (by linarith)]
    have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2])
    have hcs := one_sub_cos_le_sin ⟨ht.1.le, ht.2.le⟩
    have hsc := sin_sq_add_cos_sq t
    nlinarith
  rcases le_or_gt t θ with h2 | h2
  · rw [F_eq_two_r ⟨h1, h2⟩, r_def, if_neg (not_le.2 h1), if_pos h2]; linarith
  rcases le_or_gt t (π / 2 - φ) with h3 | h3
  · rw [F_eq_r ⟨h2, h3⟩]; exact r_pos_mid h2 h3
  · -- `F = (3 − 3x₀) sin t − cos t / 2 − 1`
    have hr : π / 2 - t ∈ Icc (0 : ℝ) φ := ⟨by linarith [ht.2], by linarith⟩
    rw [p₂_sub_dp₁, x_piece0 hr, y_piece0 hr, x_of_ge h3.le, y_of_ge h3.le, sin_pi_div_two_sub,
      cos_pi_div_two_sub]
    have hs : 1 - φ ^ 2 / 2 ≤ sin t := by
      rw [← cos_pi_div_two_sub]
      have := one_sub_sq_div_two_le_cos (x := π / 2 - t)
      have hsq : (π / 2 - t) ^ 2 ≤ φ ^ 2 := by nlinarith [hr.1, hr.2]
      linarith
    have hc := cos_le_one t
    have hsc := sin_sq_add_cos_sq t
    nlinarith

/-- **Theorem 6.1.2 for Gerver's sofa**: the cap `C(G)` satisfies the injectivity condition. -/
theorem isInjectiveCap_Kg : IsInjectiveCap Kg where
  isCap := isCap_Kg
  ac_left := sigmaK_Kg_ac_left
  ac_right := sigmaK_Kg_ac_right
  continuousOn_armFm := by
    refine (show Continuous fun t => p₂ t + 1 - dp₁ t from
      (continuous_p₂.add continuous_const).sub continuous_dp₁).continuousOn.congr ?_
    intro t ht; exact armFm_Kg ht
  continuousOn_armGp := by
    refine (show Continuous fun t => p₁ t + 1 + dp₂ t from
      (continuous_p₁.add continuous_const).add continuous_dp₂).continuousOn.congr ?_
    intro t ht; exact armGp_Kg ht
  one_lt_arm := fun t ht => by
    have hpi := Real.pi_pos
    refine ⟨?_, ?_⟩
    · rw [armFp_Kg ht.1.le ht.2]
      linarith [F_pos ht]
    · rw [armGp_Kg ⟨ht.1.le, ht.2.le⟩, add_assoc, add_comm 1, ← add_assoc, p₁_add_dp₂]
      linarith [F_pos (t := π / 2 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩]

end Sofa.GP
