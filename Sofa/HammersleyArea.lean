/-
# Sofa/HammersleyArea.lean — the area of Hammersley's sofa; `π/2 + 2/π ≤ sofaConstant`
(milestone M-H, part 2)

`volume (hsofa r) ≥ π/2 + 2r - πr²/2` via the region between the two boundary graphs
(`volume_regionBetween_eq_integral`) and `∫_{-1}^{1} √(1 - x²) = π/2`.
For `r = 2/π` this is `π/2 + 2/π ≈ 2.2074 > 2.2`.

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 1 (2026-09-17, Opus 5): compiled in the cloud dev tree
(Lean 4.33.1, Mathlib v4.33.1 with subset imports), no `sorry`; full `import Mathlib` re-check pending.
-/
import Sofa.HammersleySofa

noncomputable section

open Real Set MovingSofa MeasureTheory intervalIntegral
open scoped EuclideanGeometry RealInnerProductSpace unitInterval ENNReal

namespace Sofa

/-- Lower boundary of the sofa (the hole; it vanishes outside `[-2r, 0]`). -/
def hlo (r x : ℝ) : ℝ := √(r ^ 2 - (x + r) ^ 2)

/-- Upper boundary of the sofa. -/
def hhi (r x : ℝ) : ℝ := √(1 - (max (max (-(2 * r) - x) x) 0) ^ 2)

lemma continuous_hlo (r : ℝ) : Continuous (hlo r) := by
  unfold hlo; exact Real.continuous_sqrt.comp (by fun_prop)

lemma continuous_hhi (r : ℝ) : Continuous (hhi r) := by
  unfold hhi
  exact Real.continuous_sqrt.comp (continuous_const.sub
    ((((continuous_const.sub continuous_id).max continuous_id).max continuous_const).pow 2))

variable {r : ℝ}

lemma max_left_piece (hr0 : 0 < r) {x : ℝ} (hx : x ≤ -(2 * r)) :
    max (max (-(2 * r) - x) x) 0 = -(2 * r) - x := by
  rw [max_eq_left (by linarith : x ≤ -(2 * r) - x), max_eq_left (by linarith : (0 : ℝ) ≤ -(2 * r) - x)]

lemma max_mid_piece {x : ℝ} (hx1 : -(2 * r) ≤ x) (hx2 : x ≤ 0) :
    max (max (-(2 * r) - x) x) 0 = 0 :=
  max_eq_right (max_le (by linarith) hx2)

lemma max_right_piece (hr0 : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    max (max (-(2 * r) - x) x) 0 = x := by
  rw [max_eq_right (by linarith : -(2 * r) - x ≤ x), max_eq_left hx]

/-- The open region between the two boundaries lies in the sofa. -/
lemma pt_mem_hsofa_of_mem_regionBetween (hr0 : 0 < r) {x y : ℝ}
    (h : (x, y) ∈ regionBetween (hlo r) (hhi r) (Ioo (-(2 * r + 1)) 1)) : pt x y ∈ hsofa r := by
  obtain ⟨-, hlo_lt, hlt_hi⟩ := h
  change hlo r x < y at hlo_lt
  change y < hhi r x at hlt_hi
  simp only [mem_hsofa, pt_zero, pt_one]
  have hy0 : 0 < y := lt_of_le_of_lt (Real.sqrt_nonneg _) hlo_lt
  have hhi' : y ^ 2 < 1 - (max (max (-(2 * r) - x) x) 0) ^ 2 := by
    rw [hhi, Real.lt_sqrt hy0.le] at hlt_hi; exact hlt_hi
  refine ⟨hy0.le, ?_, ?_⟩
  · by_cases hneg : r ^ 2 - (x + r) ^ 2 ≤ 0
    · nlinarith [sq_nonneg y]
    · rw [hlo, Real.sqrt_lt' hy0] at hlo_lt
      nlinarith
  · rcases le_or_gt x (-(2 * r)) with hxl | hxl
    · rw [max_left_piece hr0 hxl] at hhi'
      exact Or.inr (Or.inr ⟨hxl, by nlinarith⟩)
    · rcases le_or_gt x 0 with hxr | hxr
      · rw [max_mid_piece hxl.le hxr] at hhi'
        exact Or.inr (Or.inl ⟨hxl.le, hxr, by nlinarith⟩)
      · rw [max_right_piece hr0 hxr.le] at hhi'
        exact Or.inl ⟨hxr.le, by nlinarith⟩

lemma measurableSet_region (r : ℝ) :
    MeasurableSet (regionBetween (hlo r) (hhi r) (Ioo (-(2 * r + 1)) 1)) :=
  measurableSet_regionBetween (continuous_hlo r).measurable (continuous_hhi r).measurable
    measurableSet_Ioo

lemma volume_region_le (hr0 : 0 < r) :
    volume (regionBetween (hlo r) (hhi r) (Ioo (-(2 * r + 1)) 1)) ≤ volume (hsofa r) := by
  have hmeas := measurableSet_region r
  calc volume (regionBetween (hlo r) (hhi r) (Ioo (-(2 * r + 1)) 1))
      = volume ((WithLp.ofLp : ℝ² → (Fin 2 → ℝ)) ⁻¹'
          (MeasurableEquiv.finTwoArrow ⁻¹'
            regionBetween (hlo r) (hhi r) (Ioo (-(2 * r + 1)) 1))) := by
        rw [(PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
            (MeasurableEquiv.finTwoArrow.measurable hmeas).nullMeasurableSet,
          (volume_preserving_finTwoArrow ℝ).measure_preimage hmeas.nullMeasurableSet]
    _ ≤ volume (hsofa r) := by
        apply measure_mono
        intro q hq
        have h : (q 0, q 1) ∈ regionBetween (hlo r) (hhi r) (Ioo (-(2 * r + 1)) 1) := hq
        rw [eq_pt q]
        exact pt_mem_hsofa_of_mem_regionBetween hr0 h

lemma hlo_le_hhi (hr0 : 0 < r) (hr1 : r ≤ 1) {x : ℝ} (hx : x ∈ Ioo (-(2 * r + 1)) 1) :
    hlo r x ≤ hhi r x := by
  obtain ⟨hx1, hx2⟩ := hx
  unfold hlo hhi
  apply Real.sqrt_le_sqrt
  rcases le_or_gt x (-(2 * r)) with hxl | hxl
  · rw [max_left_piece hr0 hxl]; nlinarith
  · rcases le_or_gt x 0 with hxr | hxr
    · rw [max_mid_piece hxl.le hxr]; nlinarith
    · rw [max_right_piece hr0 hxr.le]; nlinarith

lemma intervalIntegrable_sqrt_one_sub_sq (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => √(1 - x ^ 2)) volume a b :=
  (Real.continuous_sqrt.comp (by fun_prop)).intervalIntegrable a b

lemma integral_hhi (hr0 : 0 < r) :
    ∫ x in (-(2 * r + 1))..1, hhi r x = π / 2 + 2 * r := by
  have hc := continuous_hhi r
  have s1 := integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) (-(2 * r + 1)) (-(2 * r)))
    (hc.intervalIntegrable (μ := volume) (-(2 * r)) 1)
  have s2 := integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) (-(2 * r)) 0)
    (hc.intervalIntegrable (μ := volume) 0 1)
  have h1 : ∫ x in (-(2 * r + 1))..(-(2 * r)), hhi r x = ∫ x in (-1 : ℝ)..0, √(1 - x ^ 2) := by
    have e : ∀ x ∈ uIcc (-(2 * r + 1)) (-(2 * r)), hhi r x = √(1 - (x + 2 * r) ^ 2) := by
      intro x hx
      rw [uIcc_of_le (by linarith)] at hx
      rw [hhi, max_left_piece hr0 hx.2]
      congr 1; ring
    rw [integral_congr e, intervalIntegral.integral_comp_add_right (fun x => √(1 - x ^ 2))]
    congr 1 <;> ring
  have h2 : ∫ x in (-(2 * r))..0, hhi r x = 2 * r := by
    have e : ∀ x ∈ uIcc (-(2 * r)) 0, hhi r x = 1 := by
      intro x hx
      rw [uIcc_of_le (by linarith)] at hx
      rw [hhi, max_mid_piece hx.1 hx.2]
      simp
    rw [integral_congr e]
    simp
  have h3 : ∫ x in (0 : ℝ)..1, hhi r x = ∫ x in (0 : ℝ)..1, √(1 - x ^ 2) := by
    refine integral_congr fun x hx => ?_
    rw [uIcc_of_le zero_le_one] at hx
    rw [hhi, max_right_piece hr0 hx.1]
  have s3 := integral_add_adjacent_intervals (intervalIntegrable_sqrt_one_sub_sq (-1) 0)
    (intervalIntegrable_sqrt_one_sub_sq 0 1)
  rw [integral_sqrt_one_sub_sq] at s3
  rw [← s1, ← s2, h1, h2, h3]
  linarith

lemma integral_sqrt_sq_sub_sq (hr0 : 0 < r) :
    ∫ x in (-r)..r, √(r ^ 2 - x ^ 2) = π * r ^ 2 / 2 := by
  have hfun : ∀ x, √(r ^ 2 - x ^ 2) = r * √(1 - (x / r) ^ 2) := by
    intro x
    have e : r ^ 2 - x ^ 2 = r ^ 2 * (1 - (x / r) ^ 2) := by
      field_simp
    rw [e, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr0.le]
  simp_rw [hfun]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun x => √(1 - x ^ 2)) hr0.ne']
  rw [show -r / r = -1 by field_simp, div_self hr0.ne', integral_sqrt_one_sub_sq, smul_eq_mul]
  ring

lemma integral_hlo (hr0 : 0 < r) :
    ∫ x in (-(2 * r + 1))..1, hlo r x = π * r ^ 2 / 2 := by
  have hc := continuous_hlo r
  have s1 := integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) (-(2 * r + 1)) (-(2 * r)))
    (hc.intervalIntegrable (μ := volume) (-(2 * r)) 1)
  have s2 := integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) (-(2 * r)) 0)
    (hc.intervalIntegrable (μ := volume) 0 1)
  have h1 : ∫ x in (-(2 * r + 1))..(-(2 * r)), hlo r x = 0 := by
    have e : ∀ x ∈ uIcc (-(2 * r + 1)) (-(2 * r)), hlo r x = 0 := by
      intro x hx
      rw [uIcc_of_le (by linarith)] at hx
      rw [hlo, Real.sqrt_eq_zero']
      nlinarith [hx.2]
    rw [integral_congr e]; simp
  have h3 : ∫ x in (0 : ℝ)..1, hlo r x = 0 := by
    have e : ∀ x ∈ uIcc (0 : ℝ) 1, hlo r x = 0 := by
      intro x hx
      rw [uIcc_of_le zero_le_one] at hx
      rw [hlo, Real.sqrt_eq_zero']
      nlinarith [hx.1]
    rw [integral_congr e]; simp
  have h2 : ∫ x in (-(2 * r))..0, hlo r x = π * r ^ 2 / 2 := by
    unfold hlo
    rw [intervalIntegral.integral_comp_add_right (fun x => √(r ^ 2 - x ^ 2))]
    have e1 : -(2 * r) + r = -r := by ring
    rw [e1, zero_add, integral_sqrt_sq_sub_sq hr0]
  rw [← s1, ← s2, h1, h2, h3]
  ring

/-- **Area of Hammersley's sofa** (lower bound; equality holds but is not needed). -/
theorem volume_hsofa_ge (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ENNReal.ofReal (π / 2 + 2 * r - π * r ^ 2 / 2) ≤ volume (hsofa r) := by
  refine le_trans (le_of_eq ?_) (volume_region_le hr0)
  rw [Measure.volume_eq_prod,
    volume_regionBetween_eq_integral ((continuous_hlo r).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      ((continuous_hhi r).integrableOn_Icc.mono_set Ioo_subset_Icc_self) measurableSet_Ioo
      (fun x hx => hlo_le_hhi hr0 hr1 hx)]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
  simp only [Pi.sub_apply]
  rw [intervalIntegral.integral_sub ((continuous_hhi r).intervalIntegrable _ _)
    ((continuous_hlo r).intervalIntegrable _ _), integral_hhi hr0, integral_hlo hr0]

/-- The classical Hammersley sofa (hole radius `2/π`). -/
def hammersleySofa : Set ℝ² := hsofa (2 / π)

lemma two_div_pi_pos : 0 < 2 / π := by positivity

lemma two_div_pi_le_one : 2 / π ≤ 1 := by
  rw [div_le_one pi_pos]; exact two_le_pi

theorem isMovingSofa_hammersleySofa : IsMovingSofa hammersleySofa (hmotion (2 / π)) :=
  isMovingSofa_hsofa two_div_pi_pos two_div_pi_le_one

theorem volume_hammersleySofa_ge : ENNReal.ofReal (π / 2 + 2 / π) ≤ volume hammersleySofa := by
  have h := volume_hsofa_ge two_div_pi_pos two_div_pi_le_one
  have e : π / 2 + 2 * (2 / π) - π * (2 / π) ^ 2 / 2 = π / 2 + 2 / π := by
    field_simp
    ring
  rwa [e] at h

end Sofa

namespace MovingSofa

/-- **Hammersley's lower bound** `π/2 + 2/π ≤ sofaConstant` (improves `one_le_sofaConstant`). -/
theorem pi_div_two_add_two_div_pi_le_sofaConstant :
    ENNReal.ofReal (π / 2 + 2 / π) ≤ sofaConstant :=
  Sofa.volume_hammersleySofa_ge.trans
    (le_iSup₂ (f := fun (s : Set ℝ²) (_ : ∃ m, IsMovingSofa s m) => volume s)
      Sofa.hammersleySofa ⟨_, Sofa.isMovingSofa_hammersleySofa⟩)

lemma two_point_two_lt_pi_div_two_add_two_div_pi : (2.2 : ℝ) < π / 2 + 2 / π := by
  have h1 := Real.pi_gt_d2
  have h2 := Real.pi_lt_d2
  have h3 : 2 / 3.15 < 2 / π := div_lt_div_of_pos_left (by norm_num) (by linarith) h2
  norm_num at h3
  linarith

/-- There is a moving sofa of area `> 2.2` (needed for Baek's reduction, Thm 1.5.1). -/
theorem ofReal_two_point_two_lt_sofaConstant : ENNReal.ofReal 2.2 < sofaConstant :=
  lt_of_lt_of_le
    ((ENNReal.ofReal_lt_ofReal_iff (by linarith [two_point_two_lt_pi_div_two_add_two_div_pi])).2
      two_point_two_lt_pi_div_two_add_two_div_pi)
    pi_div_two_add_two_div_pi_le_sofaConstant

end MovingSofa
