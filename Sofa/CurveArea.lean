/-
# Sofa/CurveArea.lean — Baek §7.2–§7.3: the curve area functional

**§7.2.**  Baek's Def 7.2.6 is `J(x) = ½∫_a^b x × dx` for a continuous curve `x` of bounded
variation, with `dx` its Lebesgue–Stieltjes measure.  Every curve that Chapter 8 feeds to `J` is
*absolutely continuous* — the inner corner `x_K`, the outer corner `y_K`, the parametrised supporting
lines `l^t_K`, and segments — and for those `dx = x'(t) dt`.  So here

    `curveJ z a b := ½ ∫_a^b z(t) × z'(t) dt`                                   (Def 7.2.6)

with `z' = deriv z`; this agrees with Baek's `J` on absolutely continuous curves and is *not* claimed
to agree for curves with a singular (Cantor) part.  Segments get their closed form
`segJ p q = (p × q)/2` (Def 7.2.8, Prop 7.2.4, 7.2.5), and `curveJ_line` shows that a curve moving
along a fixed line has the `J` of the segment between its endpoints (the general form of
Baek's Thm 8.3.1).

**§7.3.**  The curve area functional of the convex arc `u^{a,b}_K` is, by Baek's Thm 7.3.2 /
Lemma 7.3.3, `½∫_{(a,b)} h_K dσ_K`; we take that as the definition `convJ`.  The analytic heart of
the chapter is then the **closed form**

    `2·curveG K a b = h_K(b) e⁺_K(b) − h_K(a) e⁺_K(a) + ∫_a^b (h_K² − (e⁺_K)²) dt`     (`two_mul_curveG_eq`)

(`e⁺_K = ⟪v⁺_K, v_t⟫ = h'_K` a.e.), proved by integration by parts against the Stieltjes measure
`σ_K = d(arcFn K)` (`Sofa/StieltjesIBP.lean`) and then against `dt`.  It gives Baek's
Lemma 7.3.4 (concatenation of convex arcs), and together with Thm 7.1.3 the classical
`|K| = ½∫_{S¹}(h_K² − h_K'²)` (`volumeReal_eq_integral_sq_sub_sq`).  Mamikon's theorem
(`Sofa/Mamikon.lean`) is a two-line consequence.

STATUS: [PROOF-C-local] round 1 (2026-09-22, Opus 5.5).
-/
import Sofa.Minkowski
import Sofa.StieltjesIBP

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace Interval

namespace Sofa

variable {K : Set ℝ²}

/-! ## The moving frame -/

/-- `(αu_t + βv_t) × (γu_t + δv_t) = αδ − βγ`. -/
lemma cross_frame (α β γ δ t : ℝ) :
    cross (α • u t + β • v t) (γ • u t + δ • v t) = α * δ - β * γ := by
  simp only [cross, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, u_coord_zero, u_coord_one,
    v_coord_zero, v_coord_one]
  linear_combination (α * δ - β * γ) * sin_sq_add_cos_sq t

/-! ## Segments (Def 7.2.8, Prop 7.2.4, Prop 7.2.5) -/

/-- **Def 7.2.8**: the curve area functional of the oriented segment from `p` to `q`. -/
def segJ (p q : ℝ²) : ℝ := cross p q / 2

lemma segJ_self (p : ℝ²) : segJ p p = 0 := by rw [segJ, cross_self, zero_div]

lemma segJ_comm (p q : ℝ²) : segJ p q = -segJ q p := by rw [segJ, segJ, cross_comm]; ring

/-- **Prop 7.2.4**: if `p ∈ l(t, h)` and `q = p + d v_t`, then `J(p, q) = h d / 2`. -/
theorem segJ_of_line {p q : ℝ²} {t h d : ℝ} (hp : ⟪p, u t⟫ = h) (hq : q = p + d • v t) :
    segJ p q = h * d / 2 := by
  rw [segJ, hq, cross_add_right, cross_self, cross_smul_right, cross_v, hp]; ring

/-- **Prop 7.2.5**: if `p`, `q` and the origin are on a common line `l(t, 0)`, then `J(p,q) = 0`. -/
theorem segJ_eq_zero_of_line_zero {p q : ℝ²} {t : ℝ} (hp : ⟪p, u t⟫ = 0) (hq : ⟪q, u t⟫ = 0) :
    segJ p q = 0 := by
  have hq' : q = p + ⟪q - p, v t⟫ • v t := by
    have h1 := decomp_u_v t (q - p)
    rw [inner_sub_left, hq, hp, sub_zero, zero_smul, zero_add] at h1
    rw [← h1]; abel
  rw [segJ_of_line hp hq', zero_mul, zero_div]

/-- `J(v⁻_K(t), v⁺_K(t)) = h_K(t)·|e_K(t)|/2`: the segment is the edge `e_K(t)`. -/
theorem segJ_vtxM_vtxP (K : Set ℝ²) (t : ℝ) :
    segJ (vtxM K t) (vtxP K t) = supportFn K t * edgeLength K t / 2 := by
  rw [segJ, vtxM, vtxP, cross_frame, edgeLength]; ring

/-! ## Curves (Def 7.2.6, Prop 7.2.2, Prop 7.2.6) -/

/-- **Def 7.2.6** for absolutely continuous curves: `J(z) = ½∫_a^b z × z'`. -/
def curveJ (z : ℝ → ℝ²) (a b : ℝ) : ℝ := (∫ t in a..b, cross (z t) (deriv z t)) / 2

/-- **Prop 7.2.2**: the bilinear form behind `curveJ`. -/
def curveB (z₁ z₂ : ℝ → ℝ²) (a b : ℝ) : ℝ := (∫ t in a..b, cross (z₁ t) (deriv z₂ t)) / 2

lemma curveJ_eq_curveB (z : ℝ → ℝ²) (a b : ℝ) : curveJ z a b = curveB z z a b := rfl

/-- **Prop 7.2.6**: concatenation. -/
theorem curveJ_add {z : ℝ → ℝ²} {a b c : ℝ}
    (hab : IntervalIntegrable (fun t => cross (z t) (deriv z t)) volume a b)
    (hbc : IntervalIntegrable (fun t => cross (z t) (deriv z t)) volume b c) :
    curveJ z a b + curveJ z b c = curveJ z a c := by
  rw [curveJ, curveJ, curveJ, ← intervalIntegral.integral_add_adjacent_intervals hab hbc]; ring

/-- `curveJ z a b` only depends on `z` on `[a, b]`. -/
theorem curveJ_congr {z z' : ℝ → ℝ²} {a b : ℝ} (hab : a ≤ b) (h : EqOn z z' (Icc a b)) :
    curveJ z a b = curveJ z' a b := by
  unfold curveJ
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  have hb : ∀ᵐ t ∂volume, t ∉ ({b} : Set ℝ) := (Set.countable_singleton b).ae_notMem volume
  filter_upwards [hb] with t htb ht
  rw [uIoc_of_le hab] at ht
  have ht' : t ∈ Ioo a b := ⟨ht.1, lt_of_le_of_ne ht.2 (by simpa using htb)⟩
  have hev : z =ᶠ[𝓝 t] z' := Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht'.1 ht'.2)
    fun x hx => h (Ioo_subset_Icc_self hx)
  rw [h (Ioo_subset_Icc_self ht'), hev.deriv_eq]

/-- **A curve moving along a fixed line** has the curve area functional of the segment joining its
endpoints.  This is the general form of Baek's Thm 8.3.1. -/
theorem curveJ_line {p d : ℝ²} {lam : ℝ → ℝ} {a b : ℝ}
    (hlam : AbsolutelyContinuousOnInterval lam a b) :
    curveJ (fun t => p + lam t • d) a b = segJ (p + lam a • d) (p + lam b • d) := by
  have hae : ∀ᵐ t ∂volume, t ∈ Ι a b →
      cross (p + lam t • d) (deriv (fun t => p + lam t • d) t) = deriv lam t * cross p d := by
    filter_upwards [hlam.ae_differentiableAt] with t ht htab
    have hd : HasDerivAt (fun t => p + lam t • d) (deriv lam t • d) t :=
      ((ht (uIoc_subset_uIcc htab)).hasDerivAt.smul_const d).const_add p
    rw [hd.deriv, cross_smul_right, cross_add_left, cross_smul_left, cross_self]; ring
  rw [curveJ, intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_mul_const,
    hlam.integral_deriv_eq_sub, segJ]
  simp only [cross_add_left, cross_add_right, cross_smul_left, cross_smul_right, cross_self]
  rw [cross_comm d p]; ring

/-! ## Analytic facts about `h_K` -/

/-- Where `σ_K` has no atom, `h_K` is differentiable with derivative `e⁺_K(t) = e⁻_K(t)`. -/
theorem hasDerivAt_supportFn_of_edgeLength_eq_zero (hK : IsCompact K) (hne : K.Nonempty) {t : ℝ}
    (h0 : edgeLength K t = 0) : HasDerivAt (supportFn K) (edgeMax K t) t := by
  have heq : edgeMin K t = edgeMax K t := by
    rw [edgeLength, sub_eq_zero] at h0; exact h0.symm
  have hr : HasDerivWithinAt (supportFn K) (edgeMax K t) (Ici t) t :=
    hasDerivWithinAt_Ioi_iff_Ici.1 (hasDerivWithinAt_supportFn_Ioi hK hne t)
  have hl : HasDerivWithinAt (supportFn K) (edgeMax K t) (Iic t) t := by
    have := hasDerivWithinAt_supportFn_Iio hK hne t
    rw [heq] at this
    exact hasDerivWithinAt_Iio_iff_Iic.1 this
  have := hl.union hr
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this

/-- `h'_K = e⁺_K` almost everywhere. -/
theorem ae_deriv_supportFn (hK : IsCompact K) (hne : K.Nonempty) :
    ∀ᵐ t ∂volume, deriv (supportFn K) t = edgeMax K t := by
  filter_upwards [(countable_edgeLength_ne_zero hK hne).ae_notMem volume] with t ht
  have h0 : edgeLength K t = 0 := by simpa using ht
  exact (hasDerivAt_supportFn_of_edgeLength_eq_zero hK hne h0).deriv

theorem lipschitzWith_supportFn (hK : IsCompact K) (hne : K.Nonempty) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ p ∈ K, ‖p‖ ≤ R) : LipschitzWith (Real.toNNReal R) (supportFn K) := by
  refine LipschitzWith.of_dist_le_mul fun s t => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hR0]
  exact abs_supportFn_sub_le hK hne hR s t

theorem absolutelyContinuousOnInterval_supportFn (hK : IsCompact K) (hne : K.Nonempty)
    (a b : ℝ) : AbsolutelyContinuousOnInterval (supportFn K) a b := by
  obtain ⟨R, hR0, hR⟩ := exists_radius hK hne
  exact (lipschitzWith_supportFn hK hne hR0 hR).lipschitzOnWith.absolutelyContinuousOnInterval

theorem measurable_edgeMax (hK : IsCompact K) (hne : K.Nonempty) : Measurable (edgeMax K) := by
  have he : edgeMax K = fun t => arcFn K t - ∫ s in (0:ℝ)..t, supportFn K s :=
    funext (edgeMax_eq_arcFn_sub K)
  rw [he]
  exact (arcFn_mono hK hne).measurable.sub (continuous_primitive_supportFn hK hne).measurable

/-- A bounded measurable function is interval integrable. -/
lemma intervalIntegrable_of_bdd {f : ℝ → ℝ} (hm : Measurable f) {C : ℝ} (hC : ∀ t, |f t| ≤ C)
    (a b : ℝ) : IntervalIntegrable f volume a b := by
  refine ⟨?_, ?_⟩ <;>
  · refine Measure.integrableOn_of_bounded (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      hm.aestronglyMeasurable (M := C) (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs]; exact hC t

lemma intervalIntegrable_edgeMax_sq (hK : IsCompact K) (hne : K.Nonempty) (a b : ℝ) :
    IntervalIntegrable (fun t => edgeMax K t ^ 2) volume a b := by
  obtain ⟨R, _, hR⟩ := exists_radius hK hne
  refine intervalIntegrable_of_bdd ((measurable_edgeMax hK hne).pow_const 2) (C := R ^ 2)
    (fun t => ?_) a b
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_edgeMax_le hK hne hR t) 2

/-- The primitive `H(t) = ∫_0^t h_K` has derivative `h_K` everywhere. -/
lemma hasDerivAt_primitive_supportFn (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    HasDerivAt (fun t => ∫ s in (0:ℝ)..t, supportFn K s) (supportFn K t) t :=
  ((continuous_supportFn hK hne).integral_hasStrictDerivAt 0 t).hasDerivAt

lemma absolutelyContinuousOnInterval_primitive_supportFn (hK : IsCompact K) (hne : K.Nonempty)
    (a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => ∫ s in (0:ℝ)..t, supportFn K s) a b := by
  have hderiv : deriv (fun t => ∫ s in (0:ℝ)..t, supportFn K s) = supportFn K :=
    funext fun t => (hasDerivAt_primitive_supportFn hK hne t).deriv
  have hC : ContDiff ℝ 1 (fun t => ∫ s in (0:ℝ)..t, supportFn K s) :=
    contDiff_one_iff_deriv.2 ⟨fun t => (hasDerivAt_primitive_supportFn hK hne t).differentiableAt,
      by rw [hderiv]; exact continuous_supportFn hK hne⟩
  exact hC.contDiffOn.absolutelyContinuousOnInterval

/-! ## The closed form of `½∫ h_K dσ_K` -/

/-- **The closed form of the convex-curve area functional**:

    `2·curveG K a b = ∫_{(a,b]} h_K dσ_K = h(b) e⁺(b) − h(a) e⁺(a) + ∫_a^b (h² − (e⁺)²)`. -/
theorem two_mul_curveG_eq (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ} (hab : a ≤ b) :
    2 * curveG K a b
      = supportFn K b * edgeMax K b - supportFn K a * edgeMax K a
        + ∫ t in a..b, (supportFn K t ^ 2 - edgeMax K t ^ 2) := by
  have hcont := continuous_supportFn hK hne
  have hac := absolutelyContinuousOnInterval_supportFn hK hne a b
  have hHac := absolutelyContinuousOnInterval_primitive_supportFn hK hne a b
  have hde := ae_deriv_supportFn hK hne
  have hHderiv : deriv (fun t => ∫ s in (0:ℝ)..t, supportFn K s) = supportFn K :=
    funext fun t => (hasDerivAt_primitive_supportFn hK hne t).deriv
  have harc : ∀ t, arcFn K t = edgeMax K t + ∫ s in (0:ℝ)..t, supportFn K s := fun t => by
    have := edgeMax_eq_arcFn_sub K t; linarith
  -- Step 1: integration by parts against `σ_K = d(arcFn K)`
  have h1 : 2 * curveG K a b = supportFn K b * arcFn K b - supportFn K a * arcFn K a
      - ∫ s in a..b, deriv (supportFn K) s * arcFn K s := by
    have := integral_Ioc_stieltjes (arcSF hK hne) hab hac
    simp only [arcSF_apply] at this
    rw [curveG, sigmaK_eq hK hne, ← this]; ring
  -- Step 2: `h' = e⁺` a.e. and `arcFn = e⁺ + H`
  have h2 : ∫ s in a..b, deriv (supportFn K) s * arcFn K s
      = ∫ s in a..b, (edgeMax K s ^ 2
          + edgeMax K s * ∫ r in (0:ℝ)..s, supportFn K r) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hde] with s hs _
    rw [hs, harc]; ring
  -- Step 3: `∫ e⁺ H = [h H] − ∫ h²` (integration by parts against `dt`)
  have h3 : ∫ s in a..b, edgeMax K s * ∫ r in (0:ℝ)..s, supportFn K r
      = supportFn K b * (∫ r in (0:ℝ)..b, supportFn K r)
        - supportFn K a * (∫ r in (0:ℝ)..a, supportFn K r)
        - ∫ s in a..b, supportFn K s ^ 2 := by
    have hibp := hHac.integral_mul_deriv_eq_deriv_mul hac
    have e1 : ∫ s in a..b, edgeMax K s * ∫ r in (0:ℝ)..s, supportFn K r
        = ∫ s in a..b, (∫ r in (0:ℝ)..s, supportFn K r) * deriv (supportFn K) s := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hde] with s hs _
      rw [hs]; ring
    have e2 : ∫ s in a..b, deriv (fun t => ∫ r in (0:ℝ)..t, supportFn K r) s * supportFn K s
        = ∫ s in a..b, supportFn K s ^ 2 := by
      rw [hHderiv]; congr 1; funext s; ring
    rw [e1, hibp, e2]; ring
  -- integrability
  have hie2 := intervalIntegrable_edgeMax_sq hK hne a b
  have hieH : IntervalIntegrable
      (fun s => edgeMax K s * ∫ r in (0:ℝ)..s, supportFn K r) volume a b :=
    (intervalIntegrable_edgeMax hK hne a b).mul_continuousOn
      (continuous_primitive_supportFn hK hne).continuousOn
  have hih2 : IntervalIntegrable (fun s => supportFn K s ^ 2) volume a b :=
    (hcont.pow 2).intervalIntegrable a b
  rw [h1, h2, intervalIntegral.integral_add hie2 hieH, h3,
    intervalIntegral.integral_sub hih2 hie2, harc, harc]
  ring

/-! ## Convex arcs (§7.3) -/

/-- **Baek Thm 7.3.2 / Lemma 7.3.3**: the curve area functional of the convex arc `u^{a,b}_K`
(from `v⁺_K(a)` to `v⁻_K(b)`) is `½∫_{(a,b)} h_K dσ_K`.  We take this as the definition. -/
def convJ (K : Set ℝ²) (a b : ℝ) : ℝ := (∫ t in Ioo a b, supportFn K t ∂(sigmaK K)) / 2

/-- `J(u^{a,b}_K)` is `curveG` minus the contribution of the atom at `b`. -/
theorem convJ_eq_curveG (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ} (hab : a < b) :
    convJ K a b = curveG K a b - supportFn K b * edgeLength K b / 2 := by
  have hdisj : Disjoint (Ioo a b) {b} := Set.disjoint_singleton_right.2 fun h => lt_irrefl _ h.2
  have hunion : Ioc a b = Ioo a b ∪ {b} := (Ioo_union_right hab).symm
  have hint : IntegrableOn (supportFn K) (Ioc a b) (sigmaK K) :=
    integrableOn_supportFn_sigmaK hK hne a b
  have hsplit : ∫ t in Ioc a b, supportFn K t ∂(sigmaK K)
      = (∫ t in Ioo a b, supportFn K t ∂(sigmaK K))
        + ∫ t in ({b} : Set ℝ), supportFn K t ∂(sigmaK K) := by
    rw [hunion, setIntegral_union hdisj (measurableSet_singleton b)
      (hint.mono_set Ioo_subset_Ioc_self) (hint.mono_set (Set.singleton_subset_iff.2 ⟨hab, le_rfl⟩))]
  have hatom : ∫ t in ({b} : Set ℝ), supportFn K t ∂(sigmaK K)
      = supportFn K b * edgeLength K b := by
    rw [integral_singleton, smul_eq_mul, Measure.real, sigmaK_singleton hK hne,
      ENNReal.toReal_ofReal (edgeLength_nonneg hK hne b), mul_comm]
  rw [convJ, curveG, hsplit, hatom]; ring

/-- **The closed form of `J(u^{a,b}_K)`**:

    `2·J(u^{a,b}_K) = h(b) e⁻(b) − h(a) e⁺(a) + ∫_a^b (h² − (e⁺)²)`. -/
theorem two_mul_convJ_eq (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ} (hab : a < b) :
    2 * convJ K a b
      = supportFn K b * edgeMin K b - supportFn K a * edgeMax K a
        + ∫ t in a..b, (supportFn K t ^ 2 - edgeMax K t ^ 2) := by
  have h := two_mul_curveG_eq hK hne hab.le
  rw [convJ_eq_curveG hK hne hab, edgeLength]
  linarith

/-- **Baek Lemma 7.3.4**: `u^{a,c}_K` is the concatenation of `u^{a,b}_K`, the edge `e_K(b)`, and
`u^{b,c}_K`. -/
theorem convJ_concat (hK : IsCompact K) (hne : K.Nonempty) {a b c : ℝ} (hab : a < b)
    (hbc : b < c) :
    convJ K a c = convJ K a b + segJ (vtxM K b) (vtxP K b) + convJ K b c := by
  have hac := two_mul_convJ_eq hK hne (hab.trans hbc)
  have h1 := two_mul_convJ_eq hK hne hab
  have h2 := two_mul_convJ_eq hK hne hbc
  have hi : ∀ x y : ℝ,
      IntervalIntegrable (fun t => supportFn K t ^ 2 - edgeMax K t ^ 2) volume x y :=
    fun x y => (((continuous_supportFn hK hne).pow 2).intervalIntegrable x y).sub
      (intervalIntegrable_edgeMax_sq hK hne x y)
  have hsplit : (∫ t in a..b, (supportFn K t ^ 2 - edgeMax K t ^ 2))
      + (∫ t in b..c, (supportFn K t ^ 2 - edgeMax K t ^ 2))
      = ∫ t in a..c, (supportFn K t ^ 2 - edgeMax K t ^ 2) :=
    intervalIntegral.integral_add_adjacent_intervals (hi a b) (hi b c)
  rw [segJ_vtxM_vtxP, edgeLength]
  linarith

/-! ## `J(u^{a,b}_K)` is quadratic in `K` (Thm 7.3.2, Lemma 7.3.3) -/

/-- **Baek Lemma 7.3.3**: the bilinear form `B(K₁, K₂) = ½∫_{(a,b)} h_{K₁} dσ_{K₂}` behind
`J(u^{a,b}_K) = B(K, K)`. -/
def convB (a b : ℝ) (A B : Set ℝ²) : ℝ := (∫ t in Ioo a b, supportFn A t ∂(sigmaK B)) / 2

lemma convB_self (K : Set ℝ²) (a b : ℝ) : convB a b K K = convJ K a b := rfl

/-- `convB` is convex-linear in its first (support-function) slot. -/
theorem convB_mix_left {A A' B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty)
    (hA' : IsCompact A') (hA'ne : A'.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (a b : ℝ) :
    convB a b (mix l A A') B = (1 - l) * convB a b A B + l * convB a b A' B := by
  have hpt : ∀ s : ℝ, supportFn (mix l A A') s = (1 - l) * supportFn A s + l * supportFn A' s :=
    fun s => supportFn_mix hA hAne hA' hA'ne hl0 hl1 s
  have i1 := (integrableOn_supportFn_sigmaK' hA hAne B a b).mono_set Ioo_subset_Ioc_self
  have i2 := (integrableOn_supportFn_sigmaK' hA' hA'ne B a b).mono_set Ioo_subset_Ioc_self
  rw [convB, convB, convB]
  simp only [hpt]
  rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
  ring

/-- `convB` is convex-linear in its second (measure) slot. -/
theorem convB_mix_right {A B B' : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty)
    (hB : IsCompact B) (hBne : B.Nonempty) (hB' : IsCompact B') (hB'ne : B'.Nonempty)
    {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (a b : ℝ) :
    convB a b A (mix l B B') = (1 - l) * convB a b A B + l * convB a b A B' := by
  have hint1 := (integrableOn_supportFn_sigmaK' hA hAne B a b).mono_set Ioo_subset_Ioc_self
  have hint2 := (integrableOn_supportFn_sigmaK' hA hAne B' a b).mono_set Ioo_subset_Ioc_self
  have hs1 : ENNReal.ofReal (1 - l) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hs2 : ENNReal.ofReal l ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [convB, convB, convB, sigmaK_mix hB hBne hB' hB'ne hl0 hl1]
  rw [Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
    integral_add_measure (hint1.smul_measure hs1) (hint2.smul_measure hs2),
    integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hl0]
  simp only [smul_eq_mul]
  ring

/-- **Baek Theorem 7.3.2 (quadraticity)**: `K ↦ J(u^{a,b}_K)` is a quadratic functional on any
convex domain of compact bodies. -/
theorem isQuadraticOn_convJ (S : Set (Set ℝ²)) (hne : ∀ A ∈ S, A.Nonempty)
    (hclosed : ∀ A ∈ S, ∀ B ∈ S, ∀ l : ℝ, 0 ≤ l → l ≤ 1 → mix l A B ∈ S)
    (hcpt : ∀ A ∈ S, IsCompact A) (a b : ℝ) :
    IsQuadraticOn (bodyDomain S hne hclosed) (fun K => convJ K a b) := by
  refine ⟨convB a b, ⟨fun A hA => ?_, fun B hB => ?_⟩, fun K _ => (convB_self K a b).symm⟩
  · intro x hx y hy l hl0 hl1
    exact convB_mix_right (hcpt A hA) (hne A hA) (hcpt x hx) (hne x hx) (hcpt y hy) (hne y hy)
      hl0 hl1 a b
  · intro x hx y hy l hl0 hl1
    exact convB_mix_left (hcpt x hx) (hne x hx) (hcpt y hy) (hne y hy) hl0 hl1 a b

/-- With Theorem 7.1.3, the classical formula `|K| = ½∫_{S¹} (h_K² − h_K'²)`. -/
theorem volumeReal_eq_integral_sq_sub_sq (hK : IsCompact K) (hconv : Convex ℝ K)
    (hint : (interior K).Nonempty) (t₀ : ℝ) :
    volume.real K = (∫ t in t₀..t₀ + 2 * π, (supportFn K t ^ 2 - edgeMax K t ^ 2)) / 2 := by
  have hne : K.Nonempty := hint.mono interior_subset
  have h := two_mul_curveG_eq hK hne (show t₀ ≤ t₀ + 2 * π by linarith [pi_pos])
  rw [supportFn_add_two_pi, edgeMax_add_two_pi] at h
  rw [volumeReal_eq_curveG_of_interior_nonempty hK hconv hint t₀]
  linarith

end Sofa
