/-
# Sofa/GerverCap.lean — the cap `K = C(G)` of Gerver's sofa; `|K| ≥ 2.2`

`G = gerversSofa` is a monotone sofa of rotation angle `π/2` (`Sofa/GerverMono.lean`); its cap
`K = C(G)` (Def 2.3.10) is the convex set `Cvx` of `Sofa/GerverConn.lean` (`Ccap_gerver`).  Here:

* the support function of `K` on `J = [0, π]`: `h_K(α) = p₁(α) + 1`, `h_K(α + π/2) = p₂(α) + 1`
  (`supportFn_Kg`, `supportFn_Kg'`), and the inner corner `x_K(α) = p₁(α) u_α + p₂(α) v_α`
  (`innerCorner_Kg`), `α ∈ [0, π/2]`;
* **`|K| ≥ 2.2`** (`area_Kg`): `K` is convex and contains the four contact points
  `C(π/2) = (4x₀ − 3, 0)`, `A(0) = (1, 0)`, `A(π/2) = (x₀, 1)`, `C(0) = (3x₀ − 2, 1)`, hence the
  trapezoid they span, of area `3 − 3x₀ ≥ 2.4` (`x₀ = x(0) ≤ 1/5`).

STATUS: [PROOF-C] round 39 (2026-09-23, Opus 5.5).
-/
import Sofa.CapThm
import Sofa.GerverMono

noncomputable section

open Real Set MeasureTheory intervalIntegral MovingSofa
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa.GP

open GC IA
open MovingSofa.GerversSofa (A B φ θ r)

/-- The cap of Gerver's sofa, `K = C(G)`. -/
abbrev Kg : Set ℝ² := Ccap gerversSofa (π / 2)

lemma isCap_Kg : IsCap Kg (π / 2) :=
  isMonotoneSofa_gerversSofa.isCap_Ccap (by positivity) le_rfl

lemma gerversSofa_subset_Kg : gerversSofa ⊆ Kg := by
  intro z hz
  rw [← Imono_gerver] at hz
  exact Imono_subset_Ccap _ _ hz

lemma supportFn_Kg_eq {t : ℝ} (ht : t ∈ Jω (π / 2)) :
    supportFn Kg t = supportFn gerversSofa t :=
  supportFn_eq_of_subset_Ccap isCap_Kg.isCompact gerversSofa_nonempty gerversSofa_subset_Kg
    subset_rfl ht

/-- The support function of `K = C(G)` in the directions `u_α`, `α ∈ [0, π/2]`. -/
lemma supportFn_Kg {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (π / 2)) : supportFn Kg α = p₁ α + 1 := by
  rw [supportFn_Kg_eq (Or.inl hα), supportFn_gerver hα]

/-- The support function of `K = C(G)` in the directions `v_α`, `α ∈ [0, π/2]`. -/
lemma supportFn_Kg' {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (π / 2)) :
    supportFn Kg (α + π / 2) = p₂ α + 1 := by
  rw [supportFn_Kg_eq (Or.inr ⟨by linarith [hα.1], by linarith [hα.2]⟩), supportFn_gerver' hα]

/-- The inner corner of `K = C(G)`: `x_K(α) = p₁(α) u_α + p₂(α) v_α`. -/
lemma innerCorner_Kg {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (π / 2)) :
    innerCorner Kg α = p₁ α • u α + p₂ α • v α := by
  rw [innerCorner, supportFn_Kg hα, supportFn_Kg' hα, add_sub_cancel_right, add_sub_cancel_right]

/-! ## `C(G) = Cvx` -/

lemma mem_para_iff (z : ℝ²) : z ∈ para (π / 2) ↔ 0 ≤ z 1 ∧ z 1 ≤ 1 := by
  simp only [para, Hstrip, Vstrip, mem_inter_iff, mem_ofPred_eq, inner_u_pi_div_two]
  tauto

lemma ca_zero (z : ℝ²) : ca 0 z = z 0 := by
  rw [ca_eq, p₁, if_pos (show (0 : ℝ) ≤ φ by linarith [bounds.1])]; simp

lemma cb_pi_div_two (z : ℝ²) : cb (π / 2) z = -z 0 - (2 - 4 * GerversSofa.x 0) := by
  rw [cb_eq, Real.sin_pi_div_two, Real.cos_pi_div_two, p_half.2]; ring

/-- `Cvx` in terms of the strip `P(π/2)` and the outer walls. -/
lemma mem_Cvx_iff_para {z : ℝ²} :
    z ∈ Cvx ↔ z ∈ para (π / 2) ∧ ∀ t ∈ Icc (0 : ℝ) (π / 2), ca t z ≤ 1 ∧ cb t z ≤ 1 := by
  have hpi := Real.pi_pos
  rw [mem_para_iff]
  constructor
  · intro hC
    obtain ⟨⟨-, hz1, hz2⟩, -, h2⟩ := mem_Cvx.1 hC
    exact ⟨⟨hz1, hz2⟩, h2⟩
  · rintro ⟨⟨hz1, hz2⟩, h⟩
    have k0 := (h 0 ⟨le_rfl, by positivity⟩).1
    have k1 := (h (π / 2) ⟨by positivity, le_rfl⟩).2
    rw [ca_zero] at k0
    rw [cb_pi_div_two] at k1
    exact mem_Cvx.2 ⟨⟨k0, hz1, hz2⟩, by linarith, h⟩

/-- **The cap of Gerver's sofa is `Cvx`.** -/
theorem Ccap_gerver : Kg = Cvx := by
  ext z
  rw [mem_Ccap_iff, mem_Cvx_iff_para]
  refine and_congr_right fun _ => forall₂_congr fun t ht => ?_
  rw [mem_QplusS_iff, supportFn_gerver ht, supportFn_gerver' ht, u_add_pi_div_two]
  simp only [ca, cb]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-! ## The trapezoid and `|K| ≥ 2.2` -/

/-- Left edge of the trapezoid, `x = 4x₀ − 3 + (1 − x₀) y`. -/
def trL (y : ℝ) : ℝ := 4 * GerversSofa.x 0 - 3 + (1 - GerversSofa.x 0) * y

/-- Right edge of the trapezoid, `x = 1 − (1 − x₀) y`. -/
def trR (y : ℝ) : ℝ := 1 - (1 - GerversSofa.x 0) * y

lemma ptC_zero : ptC 0 = pt (3 * GerversSofa.x 0 - 2) 1 := by
  rw [ptC, y_zero]; congr 1; ring

lemma ptC_pi_div_two : ptC (π / 2) = pt (4 * GerversSofa.x 0 - 3) 0 := by
  obtain ⟨p1, -⟩ := bounds
  rw [ptC, x_of_ge (β := π / 2) (by linarith), y_of_ge (β := π / 2) (by linarith)]
  congr 1; ring

lemma ptA_zero : ptA 0 = pt 1 0 := by
  obtain ⟨p1, -⟩ := bounds
  rw [ptA, sub_zero, x_of_ge (β := π / 2) (by linarith), y_of_ge (β := π / 2) (by linarith)]

lemma ptA_pi_div_two : ptA (π / 2) = pt (GerversSofa.x 0) 1 := by
  rw [ptA, sub_self, y_zero]

lemma pt_combo (a b c d s : ℝ) :
    (1 - s) • pt a b + s • pt c d = pt ((1 - s) * a + s * c) ((1 - s) * b + s * d) := by
  ext i; fin_cases i <;> simp

/-- The trapezoid lies in `Cvx`. -/
lemma pt_mem_Cvx_of_trap {x y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) (hx1 : trL y ≤ x) (hx2 : x ≤ trR y) :
    pt x y ∈ Cvx := by
  have hpi := Real.pi_pos
  obtain ⟨x01, x02⟩ := x0_bounds
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (π / 2) := ⟨le_rfl, by positivity⟩
  have h1 : π / 2 ∈ Icc (0 : ℝ) (π / 2) := ⟨by positivity, le_rfl⟩
  have hP0 := ptC_mem_Cvx h1
  have hP1 := ptC_mem_Cvx h0
  have hQ0 := ptA_mem_Cvx h0
  have hQ1 := ptA_mem_Cvx h1
  rw [ptC_pi_div_two] at hP0
  rw [ptC_zero] at hP1
  rw [ptA_zero] at hQ0
  rw [ptA_pi_div_two] at hQ1
  have hEL : pt (trL y) y ∈ Cvx := by
    have := convex_Cvx hP0 hP1 (by linarith [hy.2] : (0 : ℝ) ≤ 1 - y) hy.1 (by ring)
    rwa [pt_combo, show (1 - y) * (4 * GerversSofa.x 0 - 3) + y * (3 * GerversSofa.x 0 - 2)
      = trL y by simp only [trL]; ring, show (1 - y) * 0 + y * 1 = y by ring] at this
  have hER : pt (trR y) y ∈ Cvx := by
    have := convex_Cvx hQ0 hQ1 (by linarith [hy.2] : (0 : ℝ) ≤ 1 - y) hy.1 (by ring)
    rwa [pt_combo, show (1 - y) * 1 + y * GerversSofa.x 0 = trR y by simp only [trR]; ring,
      show (1 - y) * 0 + y * 1 = y by ring] at this
  have hRL : 0 < trR y - trL y := by
    simp only [trR, trL]; nlinarith [hy.2]
  have hne : trR y - trL y ≠ 0 := hRL.ne'
  set s := (x - trL y) / (trR y - trL y) with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith) hRL.le
  have hs1 : s ≤ 1 := (div_le_one hRL).2 (by linarith)
  have := convex_Cvx hEL hER (by linarith : (0 : ℝ) ≤ 1 - s) hs0 (by ring)
  rwa [pt_combo, show (1 - s) * trL y + s * trR y = x by rw [hs]; field_simp; ring,
    show (1 - s) * y + s * y = y by ring] at this

lemma measurableSet_trap : MeasurableSet (regionBetween trL trR (Ioo (0 : ℝ) 1)) :=
  measurableSet_regionBetween (by unfold trL; fun_prop) (by unfold trR; fun_prop) measurableSet_Ioo

lemma volume_trap_le : volume (regionBetween trL trR (Ioo (0 : ℝ) 1)) ≤ volume Cvx := by
  have hmeas := measurableSet_trap
  have hsw : MeasurableSet (Prod.swap ⁻¹' regionBetween trL trR (Ioo (0 : ℝ) 1)) :=
    measurable_swap hmeas
  calc volume (regionBetween trL trR (Ioo (0 : ℝ) 1))
      = volume (Prod.swap ⁻¹' regionBetween trL trR (Ioo (0 : ℝ) 1)) := by
        rw [Measure.volume_eq_prod,
          (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).measure_preimage
            hmeas.nullMeasurableSet]
    _ = volume ((WithLp.ofLp : ℝ² → (Fin 2 → ℝ)) ⁻¹'
          (MeasurableEquiv.finTwoArrow ⁻¹' (Prod.swap ⁻¹' regionBetween trL trR (Ioo (0 : ℝ) 1)))) := by
        rw [(PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage
            (MeasurableEquiv.finTwoArrow.measurable hsw).nullMeasurableSet,
          (volume_preserving_finTwoArrow ℝ).measure_preimage hsw.nullMeasurableSet]
    _ ≤ volume Cvx := by
        apply measure_mono
        intro q hq
        have h : (q 1, q 0) ∈ regionBetween trL trR (Ioo (0 : ℝ) 1) := hq
        obtain ⟨hy, hx1, hx2⟩ := h
        rw [eq_pt q]
        exact pt_mem_Cvx_of_trap ⟨hy.1.le, hy.2.le⟩ hx1.le hx2.le

lemma volume_trap : volume (regionBetween trL trR (Ioo (0 : ℝ) 1))
    = ENNReal.ofReal (3 - 3 * GerversSofa.x 0) := by
  obtain ⟨x01, x02⟩ := x0_bounds
  rw [Measure.volume_eq_prod, volume_regionBetween_eq_integral
    ((by unfold trL; fun_prop : Continuous trL).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    ((by unfold trR; fun_prop : Continuous trR).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    measurableSet_Ioo (fun y hy => by simp only [trL, trR]; nlinarith [hy.2])]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have hd : ∀ y ∈ uIcc (0 : ℝ) 1, HasDerivAt
      (fun y => (4 - 4 * GerversSofa.x 0) * y - (1 - GerversSofa.x 0) * (y * y)) ((trR - trL) y) y := by
    intro y _
    have h := ((hasDerivAt_id' y).const_mul (4 - 4 * GerversSofa.x 0)).sub
      (((hasDerivAt_id' y).mul (hasDerivAt_id' y)).const_mul (1 - GerversSofa.x 0))
    refine h.congr_deriv ?_
    simp only [Pi.sub_apply, trL, trR]; ring
  have hc : Continuous (trR - trL) :=
    (by unfold trR; fun_prop : Continuous trR).sub (by unfold trL; fun_prop : Continuous trL)
  rw [integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  ring

/-- **`|C(G)| ≥ 2.2`** (the field `area` of `GerverTails`). -/
theorem area_Kg : 11 / 5 ≤ volume.real Kg := by
  obtain ⟨x01, x02⟩ := x0_bounds
  have hle : ENNReal.ofReal (3 - 3 * GerversSofa.x 0) ≤ volume Kg := by
    rw [Ccap_gerver, ← volume_trap]; exact volume_trap_le
  have hfin : volume Kg ≠ ⊤ := isCap_Kg.isCompact.measure_lt_top.ne
  have := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_ofReal (by linarith)] at this
  simp only [Measure.real]
  linarith

end Sofa.GP
