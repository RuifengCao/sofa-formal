/-
# Sofa/NicheCore.lean — Baek Lemma 8.2.3 and Theorem 8.2.4 (`A(K) ≤ 𝒬(K, B_K, D_K)`)

* For an injective cap, `σ_K` has no atoms in `[0, π/2) ∪ (π/2, π]`, so the inner corner `x_K` is
  differentiable on `(0, π/2)` with `x_K' = (1 − f)u_t + (g − 1)v_t` and `X' = ⟪x_K', e₀⟫ < 0`: the core
  `x_K|[φ, π/2 − φ]` is a graph `η = c(ξ)` over `[ξ_L, ξ_R]` (`c = Y ∘ X⁻¹`).
* **Lemma 8.2.3** without Green's theorem: with `U = d` (the line `d^L_K`) left of `ξ_L`, `U = c` on
  `(ξ_L, ξ_R)`, `U = b` (the line `b^R_K`) right of `ξ_R`, the region `Ω = {0 < η < U(ξ)}` lies in
  `N(K) \ H̆^R \ H̆^L`, `|Ω| = ∫U⁺`, and `J(W^R, x^R) + J(x_K) + J(x^L, Z^L) ≤ ∫U⁺` (integration by parts,
  the substitution `ξ = X(t)`, and `U ≤ min(b, d)`).
* **Theorem 8.2.4**: `A(K) ≤ 𝒬(K, B_K, D_K)`.

STATUS: [PROOF-C-local] round 1 (2026-09-22, Opus 5.5).
-/
import Sofa.AbsCont
import Sofa.NicheSide

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace Interval

namespace Sofa

variable {K : Set ℝ²} {φ : ℝ}

/-! ## No atoms, and the derivative of the inner corner -/

lemma IsInjectiveCap.edgeLength_eq_zero_left (hK : IsInjectiveCap K) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < π / 2) : edgeLength K t = 0 := by
  have hKc := hK.isCap.isCompact
  have hne := hK.isCap.nonempty
  have h1 : (sigmaK K).restrict (Ico 0 (π / 2)) {t} = 0 := hK.ac_left Real.volume_singleton
  rw [Measure.restrict_apply (measurableSet_singleton t),
    singleton_inter_of_mem (show t ∈ Ico 0 (π / 2) from ⟨ht0, ht⟩),
    sigmaK_singleton hKc hne, ENNReal.ofReal_eq_zero] at h1
  exact le_antisymm h1 (edgeLength_nonneg hKc hne t)

lemma IsInjectiveCap.edgeLength_eq_zero_right (hK : IsInjectiveCap K) {t : ℝ} (ht0 : π / 2 < t)
    (ht : t ≤ π) : edgeLength K t = 0 := by
  have hKc := hK.isCap.isCompact
  have hne := hK.isCap.nonempty
  have h1 : (sigmaK K).restrict (Ioc (π / 2) π) {t} = 0 := hK.ac_right Real.volume_singleton
  rw [Measure.restrict_apply (measurableSet_singleton t),
    singleton_inter_of_mem (show t ∈ Ioc (π / 2) π from ⟨ht0, ht⟩),
    sigmaK_singleton hKc hne, ENNReal.ofReal_eq_zero] at h1
  exact le_antisymm h1 (edgeLength_nonneg hKc hne t)

/-- For an injective cap, `x_K` is differentiable on `(0, π/2)`. -/
lemma IsInjectiveCap.hasDerivAt_innerCorner (hK : IsInjectiveCap K) {t : ℝ} (ht0 : 0 < t)
    (ht : t < π / 2) :
    HasDerivAt (innerCorner K) ((1 - armFp K t) • u t + (armGp K t - 1) • v t) t := by
  have hKc := hK.isCap.isCompact
  have hne := hK.isCap.nonempty
  have h1 := hasDerivAt_supportFn_of_edgeLength_eq_zero hKc hne
    (hK.edgeLength_eq_zero_left ht0.le ht)
  have h2 := (hasDerivAt_supportFn_of_edgeLength_eq_zero hKc hne
    (hK.edgeLength_eq_zero_right (t := t + π / 2) (by linarith) (by linarith))).comp_add_const
    t (π / 2)
  have hA := (h1.sub_const 1).smul (hasDerivAt_u t)
  have hB := (h2.sub_const 1).smul (hasDerivAt_v t)
  have e : innerCorner K
      = fun s => (supportFn K s - 1) • u s + (supportFn K (s + π / 2) - 1) • v s := by
    funext s; rfl
  rw [e]
  refine (hA.add hB).congr_deriv ?_
  rw [armFp_eq, armGp_eq_add]
  module

/-- `f⁺_K = f⁻_K` on `(0, π/2)` for an injective cap. -/
lemma IsInjectiveCap.armFp_eq_armFm (hK : IsInjectiveCap K) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < π / 2) : armFp K t = armFm K t := by
  have h := hK.edgeLength_eq_zero_left ht0 ht
  rw [edgeLength, sub_eq_zero] at h
  rw [armFp_eq, armFm_eq, h]

lemma IsInjectiveCap.continuousOn_armFp (hK : IsInjectiveCap K) {a b : ℝ} (ha : 0 ≤ a)
    (hb : b < π / 2) : ContinuousOn (armFp K) (Icc a b) :=
  (hK.continuousOn_armFm.mono (Icc_subset_Icc ha hb.le)).congr fun _ ht =>
    hK.armFp_eq_armFm (ha.trans ht.1) (lt_of_le_of_lt ht.2 hb)

/-! ## The coordinates of the core -/

/-- `X(t) = ⟪x_K(t), e₀⟫`. -/
def coreX (K : Set ℝ²) (t : ℝ) : ℝ := ⟪innerCorner K t, u 0⟫

/-- `Y(t) = ⟪x_K(t), e₁⟫`. -/
def coreY (K : Set ℝ²) (t : ℝ) : ℝ := ⟪innerCorner K t, u (π / 2)⟫

/-- `X'(t) = (1 − f) cos t − (g − 1) sin t`. -/
def coreX' (K : Set ℝ²) (t : ℝ) : ℝ := (1 - armFp K t) * cos t - (armGp K t - 1) * sin t

/-- `Y'(t) = (1 − f) sin t + (g − 1) cos t`. -/
def coreY' (K : Set ℝ²) (t : ℝ) : ℝ := (1 - armFp K t) * sin t + (armGp K t - 1) * cos t

lemma IsInjectiveCap.hasDerivAt_coreX (hK : IsInjectiveCap K) {t : ℝ} (ht0 : 0 < t)
    (ht : t < π / 2) : HasDerivAt (coreX K) (coreX' K t) t := by
  have h := (hK.hasDerivAt_innerCorner ht0 ht).inner (𝕜 := ℝ) (hasDerivAt_const t (u 0))
  refine h.congr_deriv ?_
  rw [inner_zero_right, zero_add, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_u_u_eq_cos, inner_v_u_eq_sin, sub_zero, zero_sub, sin_neg, coreX']
  ring

lemma IsInjectiveCap.hasDerivAt_coreY (hK : IsInjectiveCap K) {t : ℝ} (ht0 : 0 < t)
    (ht : t < π / 2) : HasDerivAt (coreY K) (coreY' K t) t := by
  have h := (hK.hasDerivAt_innerCorner ht0 ht).inner (𝕜 := ℝ) (hasDerivAt_const t (u (π / 2)))
  refine h.congr_deriv ?_
  rw [inner_zero_right, zero_add, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_u_u_eq_cos, inner_v_u_eq_sin, cos_sub_pi_div_two, sin_pi_div_two_sub, coreY']

lemma IsInjectiveCap.coreX'_neg (hK : IsInjectiveCap K) {t : ℝ} (ht0 : 0 < t)
    (ht : t < π / 2) : coreX' K t < 0 := by
  obtain ⟨hf, hg⟩ := hK.one_lt_arm t ⟨ht0, ht⟩
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], ht⟩
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 (by linarith [pi_pos])
  unfold coreX'
  nlinarith [mul_pos (sub_pos.2 hf) hc, mul_pos (sub_pos.2 hg) hs]

lemma IsInjectiveCap.continuousOn_coreX' (hK : IsInjectiveCap K) {a b : ℝ} (ha : 0 ≤ a)
    (hb : b < π / 2) : ContinuousOn (coreX' K) (Icc a b) := by
  have hf := hK.continuousOn_armFp ha hb
  have hg := hK.continuousOn_armGp.mono (Icc_subset_Icc ha hb.le)
  unfold coreX'
  exact ((continuousOn_const.sub hf).mul continuous_cos.continuousOn).sub
    ((hg.sub continuousOn_const).mul continuous_sin.continuousOn)

lemma IsInjectiveCap.continuousOn_coreY' (hK : IsInjectiveCap K) {a b : ℝ} (ha : 0 ≤ a)
    (hb : b < π / 2) : ContinuousOn (coreY' K) (Icc a b) := by
  have hf := hK.continuousOn_armFp ha hb
  have hg := hK.continuousOn_armGp.mono (Icc_subset_Icc ha hb.le)
  unfold coreY'
  exact ((continuousOn_const.sub hf).mul continuous_sin.continuousOn).add
    ((hg.sub continuousOn_const).mul continuous_cos.continuousOn)

lemma continuous_coreX (hK : IsCompact K) (hne : K.Nonempty) : Continuous (coreX K) :=
  (continuous_innerCorner hK hne).inner continuous_const

lemma continuous_coreY (hK : IsCompact K) (hne : K.Nonempty) : Continuous (coreY K) :=
  (continuous_innerCorner hK hne).inner continuous_const

lemma inner_deriv_u_zero (K : Set ℝ²) (t : ℝ) :
    ⟪(1 - armFp K t) • u t + (armGp K t - 1) • v t, u 0⟫ = coreX' K t := by
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u_eq_cos,
    inner_v_u_eq_sin, sub_zero, zero_sub, sin_neg, coreX']
  ring

lemma inner_deriv_u_pi_div_two (K : Set ℝ²) (t : ℝ) :
    ⟪(1 - armFp K t) • u t + (armGp K t - 1) • v t, u (π / 2)⟫ = coreY' K t := by
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u_eq_cos,
    inner_v_u_eq_sin, cos_sub_pi_div_two, sin_pi_div_two_sub, coreY']

lemma cross_eq_inner (p q : ℝ²) :
    cross p q = ⟪p, u 0⟫ * ⟪q, u (π / 2)⟫ - ⟪p, u (π / 2)⟫ * ⟪q, u 0⟫ := by
  rw [inner_u_zero, inner_u_zero, inner_u_pi_div_two, inner_u_pi_div_two]; rfl

/-! ## `J` of the core -/

/-- `J(x_K|[a,b]) = ½(X(b)Y(b) − X(a)Y(a)) − ∫_a^b Y X'`. -/
theorem IsInjectiveCap.curveJ_core (hK : IsInjectiveCap K) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < π / 2) :
    curveJ (innerCorner K) a b = (coreX K b * coreY K b - coreX K a * coreY K a) / 2
      - ∫ t in a..b, coreY K t * coreX' K t := by
  have hKc := hK.isCap.isCompact
  have hne := hK.isCap.nonempty
  have hmem : ∀ t ∈ uIcc a b, 0 < t ∧ t < π / 2 := fun t ht => by
    rw [uIcc_of_le hab] at ht; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcross : ∀ t ∈ uIcc a b, cross (innerCorner K t) (deriv (innerCorner K) t)
      = coreX K t * coreY' K t - coreY K t * coreX' K t := fun t ht => by
    rw [(hK.hasDerivAt_innerCorner (hmem t ht).1 (hmem t ht).2).deriv, cross_eq_inner,
      inner_deriv_u_zero, inner_deriv_u_pi_div_two]
    rfl
  have hX' := (hK.continuousOn_coreX' ha.le hb).intervalIntegrable_of_Icc (μ := volume) hab
  have hY' := (hK.continuousOn_coreY' ha.le hb).intervalIntegrable_of_Icc (μ := volume) hab
  have hXc := (continuous_coreX hKc hne).continuousOn (s := Icc a b)
  have hYc := (continuous_coreY hKc hne).continuousOn (s := Icc a b)
  have hi1 : IntervalIntegrable (fun t => coreX K t * coreY' K t) volume a b :=
    (hXc.mul (hK.continuousOn_coreY' ha.le hb)).intervalIntegrable_of_Icc (μ := volume) hab
  have hi2 : IntervalIntegrable (fun t => coreY K t * coreX' K t) volume a b :=
    (hYc.mul (hK.continuousOn_coreX' ha.le hb)).intervalIntegrable_of_Icc (μ := volume) hab
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := coreX K) (v := coreY K) (u' := coreX' K) (v' := coreY' K)
    (fun t ht => hK.hasDerivAt_coreX (hmem t ht).1 (hmem t ht).2)
    (fun t ht => hK.hasDerivAt_coreY (hmem t ht).1 (hmem t ht).2) hX' hY'
  have hswap : ∫ t in a..b, coreX' K t * coreY K t = ∫ t in a..b, coreY K t * coreX' K t := by
    congr 1; funext t; ring
  rw [curveJ, intervalIntegral.integral_congr hcross, intervalIntegral.integral_sub hi1 hi2,
    hparts, hswap]
  ring

/-- The core is a graph over the `x`-axis: with `c = Y ∘ X⁻¹`,
`∫_{X(b)}^{X(a)} c = −∫_a^b Y X'` (one-dimensional change of variables). -/
theorem IsInjectiveCap.integral_core_graph (hK : IsInjectiveCap K) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (hb : b < π / 2) :
    StrictAntiOn (coreX K) (Icc a b) ∧ coreX K '' Icc a b = Icc (coreX K b) (coreX K a) ∧
    IntegrableOn (fun ξ => coreY K (Function.invFunOn (coreX K) (Icc a b) ξ))
      (Icc (coreX K b) (coreX K a)) ∧
    (∫ ξ in (coreX K b)..(coreX K a), coreY K (Function.invFunOn (coreX K) (Icc a b) ξ))
      = -∫ t in a..b, coreY K t * coreX' K t := by
  have hKc := hK.isCap.isCompact
  have hne := hK.isCap.nonempty
  set s := Icc a b with hs
  have hin : ∀ t ∈ s, 0 < t ∧ t < π / 2 := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hanti : StrictAntiOn (coreX K) s := by
    refine strictAntiOn_of_deriv_neg (convex_Icc a b) (continuous_coreX hKc hne).continuousOn
      fun t ht => ?_
    rw [interior_Icc] at ht
    rw [(hK.hasDerivAt_coreX (by linarith [ht.1]) (by linarith [ht.2])).deriv]
    exact hK.coreX'_neg (by linarith [ht.1]) (by linarith [ht.2])
  have hinj : InjOn (coreX K) s := hanti.injOn
  have himg : coreX K '' s = Icc (coreX K b) (coreX K a) :=
    Subset.antisymm hanti.antitoneOn.image_Icc_subset
      (intermediate_value_Icc' hab.le (continuous_coreX hKc hne).continuousOn)
  have hderiv : ∀ t ∈ s, HasDerivWithinAt (coreX K) (coreX' K t) s t := fun t ht =>
    (hK.hasDerivAt_coreX (hin t ht).1 (hin t ht).2).hasDerivWithinAt
  set c := fun ξ => coreY K (Function.invFunOn (coreX K) s ξ) with hc
  have hcX : ∀ t ∈ s, c (coreX K t) = coreY K t := fun t ht => by
    simp only [hc]; rw [hinj.leftInvOn_invFunOn ht]
  have habs : ∀ t ∈ s, |coreX' K t| • c (coreX K t) = -(coreY K t * coreX' K t) := fun t ht => by
    rw [hcX t ht, abs_of_neg (hK.coreX'_neg (hin t ht).1 (hin t ht).2), smul_eq_mul]; ring
  have hcont : ContinuousOn (fun t => -(coreY K t * coreX' K t)) s :=
    ((continuous_coreY hKc hne).continuousOn.mul (hK.continuousOn_coreX' ha.le hb)).neg
  have hint : IntegrableOn c (Icc (coreX K b) (coreX K a)) := by
    rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc hderiv hinj]
    exact (hcont.integrableOn_Icc).congr_fun (fun t ht => (habs t ht).symm) measurableSet_Icc
  refine ⟨hanti, himg, hint, ?_⟩
  have hXab : coreX K b ≤ coreX K a := (hanti ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab).le
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hderiv hinj c
  rw [himg] at hcv
  rw [intervalIntegral.integral_of_le hXab, ← integral_Icc_eq_integral_Ioc, hcv,
    setIntegral_congr_fun measurableSet_Icc habs, integral_neg, intervalIntegral.integral_of_le
    hab.le, integral_Icc_eq_integral_Ioc]

/-! ## The one-dimensional inequality -/

/-- The piecewise upper boundary `U = d | c | b`. -/
def coreRoof (d c b : ℝ → ℝ) (ξL ξR : ℝ) (ξ : ℝ) : ℝ :=
  if ξ ≤ ξL then d ξ else if ξ < ξR then c ξ else b ξ

lemma integrableOn_coreRoof {d c b : ℝ → ℝ} {ξL ξR : ℝ} (hLR : ξL < ξR) (hd : Continuous d)
    (hb : Continuous b) (hc : IntegrableOn c (Icc ξL ξR)) (p q : ℝ) :
    IntegrableOn (coreRoof d c b ξL ξR) (Icc p q) := by
  have hsub : Icc p q ⊆ (Icc p q ∩ Iic ξL) ∪ (Icc p q ∩ Ioo ξL ξR) ∪ (Icc p q ∩ Ici ξR) := by
    intro ξ hξ
    by_cases h1 : ξ ≤ ξL
    · exact Or.inl (Or.inl ⟨hξ, h1⟩)
    · by_cases h2 : ξ < ξR
      · exact Or.inl (Or.inr ⟨hξ, lt_of_not_ge h1, h2⟩)
      · exact Or.inr ⟨hξ, le_of_not_gt h2⟩
  refine IntegrableOn.mono_set ?_ hsub
  refine IntegrableOn.union (IntegrableOn.union ?_ ?_) ?_
  · refine ((hd.integrableOn_Icc (a := p) (b := q)).mono_set inter_subset_left).congr_fun
      (fun ξ hξ => ?_) (measurableSet_Icc.inter measurableSet_Iic)
    rw [coreRoof, if_pos (show ξ ≤ ξL from hξ.2)]
  · refine ((hc.mono_set Ioo_subset_Icc_self).mono_set inter_subset_right).congr_fun
      (fun ξ hξ => ?_) (measurableSet_Icc.inter measurableSet_Ioo)
    simp only [coreRoof, if_neg (not_le.2 hξ.2.1), if_pos hξ.2.2]
  · refine ((hb.integrableOn_Icc (a := p) (b := q)).mono_set inter_subset_left).congr_fun
      (fun ξ hξ => ?_) (measurableSet_Icc.inter measurableSet_Ici)
    have h2 : ξR ≤ ξ := hξ.2
    have h1 : ¬ ξ ≤ ξL := not_le.2 (lt_of_lt_of_le hLR h2)
    rw [coreRoof, if_neg h1, if_neg (not_lt.2 h2)]

lemma coreRoof_of_le {d c b : ℝ → ℝ} {ξL ξR ξ : ℝ} (h : ξ ≤ ξL) :
    coreRoof d c b ξL ξR ξ = d ξ := by
  rw [coreRoof, if_pos h]

lemma coreRoof_of_mem {d c b : ℝ → ℝ} {ξL ξR ξ : ℝ} (h1 : ξL < ξ) (h2 : ξ < ξR) :
    coreRoof d c b ξL ξR ξ = c ξ := by
  rw [coreRoof, if_neg (not_le.2 h1), if_pos h2]

lemma coreRoof_of_ge {d c b : ℝ → ℝ} {ξL ξR ξ : ℝ} (hLR : ξL < ξR) (h : ξR ≤ ξ) :
    coreRoof d c b ξL ξR ξ = b ξ := by
  rw [coreRoof, if_neg (not_le.2 (lt_of_lt_of_le hLR h)), if_neg (not_lt.2 h)]

lemma coreRoof_le_d {d c b : ℝ → ℝ} {ξL ξR : ℝ} (hLR : ξL < ξR)
    (hcd : ∀ ξ ∈ Icc ξL ξR, c ξ ≤ d ξ) (hbd : ∀ ξ, ξR ≤ ξ → b ξ ≤ d ξ) (ξ : ℝ) :
    coreRoof d c b ξL ξR ξ ≤ d ξ := by
  by_cases h1 : ξ ≤ ξL
  · rw [coreRoof_of_le h1]
  · by_cases h2 : ξ < ξR
    · rw [coreRoof_of_mem (not_le.1 h1) h2]; exact hcd ξ ⟨(not_le.1 h1).le, h2.le⟩
    · rw [coreRoof_of_ge hLR (not_lt.1 h2)]; exact hbd ξ (not_lt.1 h2)

lemma coreRoof_le_b {d c b : ℝ → ℝ} {ξL ξR : ℝ} (hLR : ξL < ξR)
    (hcb : ∀ ξ ∈ Icc ξL ξR, c ξ ≤ b ξ) (hdb : ∀ ξ, ξ ≤ ξL → d ξ ≤ b ξ) (ξ : ℝ) :
    coreRoof d c b ξL ξR ξ ≤ b ξ := by
  by_cases h1 : ξ ≤ ξL
  · rw [coreRoof_of_le h1]; exact hdb ξ h1
  · by_cases h2 : ξ < ξR
    · rw [coreRoof_of_mem (not_le.1 h1) h2]; exact hcb ξ ⟨(not_le.1 h1).le, h2.le⟩
    · rw [coreRoof_of_ge hLR (not_lt.1 h2)]

/-- **The one-dimensional heart of Lemma 8.2.3.** -/
theorem integral_pieces_le {d c b : ℝ → ℝ} {Z W ξL ξR : ℝ} (hLR : ξL < ξR) (hZW : Z ≤ W)
    (hd : Continuous d) (hb : Continuous b) (hc : IntegrableOn c (Icc ξL ξR))
    (hcd : ∀ ξ ∈ Icc ξL ξR, c ξ ≤ d ξ) (hcb : ∀ ξ ∈ Icc ξL ξR, c ξ ≤ b ξ)
    (hbd : ∀ ξ, ξR ≤ ξ → b ξ ≤ d ξ) (hdb : ∀ ξ, ξ ≤ ξL → d ξ ≤ b ξ) :
    (∫ ξ in Z..ξL, d ξ) + (∫ ξ in ξL..ξR, c ξ) + (∫ ξ in ξR..W, b ξ)
      ≤ ∫ ξ in Ioo Z W, max (coreRoof d c b ξL ξR ξ) 0 := by
  have hUi : ∀ p q, IntervalIntegrable (coreRoof d c b ξL ξR) volume p q := fun p q =>
    (integrableOn_coreRoof hLR hd hb hc (p ⊓ q) (p ⊔ q)).intervalIntegrable
  have hUd := coreRoof_le_d hLR hcd hbd
  have hUb := coreRoof_le_b hLR hcb hdb
  have hA : ∫ ξ in ξL..ξR, c ξ = ∫ ξ in ξL..ξR, coreRoof d c b ξL ξR ξ := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(countable_singleton ξR).ae_notMem volume] with ξ hξ hmem
    rw [uIoc_of_le hLR.le] at hmem
    rw [coreRoof_of_mem hmem.1 (lt_of_le_of_ne hmem.2 (by simpa using hξ))]
  have hB : ∫ ξ in Z..ξL, d ξ ≤ ∫ ξ in Z..ξL, coreRoof d c b ξL ξR ξ := by
    rcases le_or_gt Z ξL with h | h
    · refine le_of_eq (intervalIntegral.integral_congr fun ξ hξ => ?_)
      rw [uIcc_of_le h] at hξ
      rw [coreRoof_of_le hξ.2]
    · rw [intervalIntegral.integral_symm ξL Z, intervalIntegral.integral_symm ξL Z]
      exact neg_le_neg (intervalIntegral.integral_mono_on h.le (hUi ξL Z)
        (hd.intervalIntegrable _ _) fun ξ _ => hUd ξ)
  have hC : ∫ ξ in ξR..W, b ξ ≤ ∫ ξ in ξR..W, coreRoof d c b ξL ξR ξ := by
    rcases le_or_gt ξR W with h | h
    · refine le_of_eq (intervalIntegral.integral_congr fun ξ hξ => ?_)
      rw [uIcc_of_le h] at hξ
      rw [coreRoof_of_ge hLR hξ.1]
    · rw [intervalIntegral.integral_symm W ξR, intervalIntegral.integral_symm W ξR]
      exact neg_le_neg (intervalIntegral.integral_mono_on h.le (hUi W ξR)
        (hb.intervalIntegrable _ _) fun ξ _ => hUb ξ)
  have hD : (∫ ξ in Z..ξL, coreRoof d c b ξL ξR ξ) + (∫ ξ in ξL..ξR, coreRoof d c b ξL ξR ξ)
      + (∫ ξ in ξR..W, coreRoof d c b ξL ξR ξ) = ∫ ξ in Z..W, coreRoof d c b ξL ξR ξ := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hUi Z ξL) (hUi ξL ξR),
      intervalIntegral.integral_add_adjacent_intervals (hUi Z ξR) (hUi ξR W)]
  have hpos : IntegrableOn (fun ξ => max (coreRoof d c b ξL ξR ξ) 0) (uIcc Z W) :=
    Integrable.pos_part (integrableOn_coreRoof hLR hd hb hc (Z ⊓ W) (Z ⊔ W))
  have hE : ∫ ξ in Z..W, coreRoof d c b ξL ξR ξ ≤ ∫ ξ in Z..W, max (coreRoof d c b ξL ξR ξ) 0 :=
    intervalIntegral.integral_mono_on hZW (hUi Z W) hpos.intervalIntegrable
      fun ξ _ => le_max_left _ _
  have hE2 : ∫ ξ in Z..W, max (coreRoof d c b ξL ξR ξ) 0
      = ∫ ξ in Ioo Z W, max (coreRoof d c b ξL ξR ξ) 0 := by
    rw [intervalIntegral.integral_of_le hZW, integral_Ioc_eq_integral_Ioo]
  linarith

/-- The region under a graph: `|{Z < ξ < W, 0 < η < U(ξ)}| = ∫ U⁺`. -/
theorem volume_underGraph {U : ℝ → ℝ} {Z W : ℝ} (hU : IntegrableOn U (Ioo Z W)) :
    volume {q : ℝ² | q 0 ∈ Ioo Z W ∧ 0 < q 1 ∧ q 1 < U (q 0)}
      = ENNReal.ofReal (∫ ξ in Ioo Z W, max (U ξ) 0) := by
  let e : ℝ² ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e volume volume :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
      (volume_preserving_finTwoArrow ℝ)
  have hset : {q : ℝ² | q 0 ∈ Ioo Z W ∧ 0 < q 1 ∧ q 1 < U (q 0)}
      = e ⁻¹' regionBetween (fun _ => (0 : ℝ)) (fun ξ => max (U ξ) 0) (Ioo Z W) := by
    ext q
    have h1 : (e q).1 = q 0 := rfl
    have h2 : (e q).2 = q 1 := rfl
    simp only [mem_ofPred_eq, mem_preimage, regionBetween, h1, h2, mem_Ioo]
    constructor
    · rintro ⟨hZ, h0, hU'⟩
      exact ⟨hZ, h0, lt_max_of_lt_left hU'⟩
    · rintro ⟨hZ, h0, hU'⟩
      refine ⟨hZ, h0, ?_⟩
      rcases lt_max_iff.1 hU' with h | h
      · exact h
      · linarith
  rw [hset, he.measure_preimage_equiv, Measure.volume_eq_prod,
    volume_regionBetween_eq_integral (integrableOn_const measure_Ioo_lt_top.ne)
      (Integrable.pos_part hU) measurableSet_Ioo
      (fun ξ _ => le_max_right _ _)]
  simp only [Pi.sub_apply, sub_zero]

/-! ## Lemma 8.2.3 -/

lemma integral_affine (m k p q : ℝ) :
    ∫ ξ in p..q, (m * ξ + k) = (q - p) * ((m * p + k) + (m * q + k)) / 2 := by
  have h1 : IntervalIntegrable (fun ξ : ℝ => m * ξ) volume p q :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma inner_innerCorner_eq_coords (K : Set ℝ²) (t θ : ℝ) :
    ⟪innerCorner K t, u θ⟫ = coreX K t * cos θ + coreY K t * sin θ := by
  rw [inner_u_decomp, coreX, coreY, inner_u_zero, inner_u_pi_div_two]

/-- The line `d^L_K` as a graph: `η = d(ξ)`. -/
def coreD (φ : ℝ) (K : Set ℝ²) (ξ : ℝ) : ℝ := (ξ * cos φ + (supportFn K (π - φ) - 1)) / sin φ

/-- The line `b^R_K` as a graph: `η = b(ξ)`. -/
def coreB (φ : ℝ) (K : Set ℝ²) (ξ : ℝ) : ℝ := (supportFn K φ - 1 - ξ * cos φ) / sin φ

/-- The core as a graph: `c = Y ∘ X⁻¹`. -/
def coreC (φ : ℝ) (K : Set ℝ²) (ξ : ℝ) : ℝ :=
  coreY K (Function.invFunOn (coreX K) (Icc φ (π / 2 - φ)) ξ)

/-- The upper boundary `U = d | c | b` of the core region. -/
def coreU (φ : ℝ) (K : Set ℝ²) : ℝ → ℝ :=
  coreRoof (coreD φ K) (coreC φ K) (coreB φ K) (coreX K (π / 2 - φ)) (coreX K φ)

lemma continuous_coreD (φ : ℝ) (K : Set ℝ²) : Continuous (coreD φ K) := by
  unfold coreD; fun_prop

lemma continuous_coreB (φ : ℝ) (K : Set ℝ²) : Continuous (coreB φ K) := by
  unfold coreB; fun_prop

lemma core_aux1 {c s k : ℝ} (hc : c ≠ 0) (hs : s ≠ 0) :
    c / s * ((1 - k) / c) + (k - 1) / s = 0 := by
  field_simp; ring

lemma core_aux2 {c s X Y k : ℝ} (hs : s ≠ 0) (h : X * -c + Y * s = k - 1) :
    c / s * X + (k - 1) / s = Y := by
  rw [← h]; field_simp; ring

lemma core_aux3 {c s X Y k : ℝ} (hs : s ≠ 0) (h : X * c + Y * s = k - 1) :
    -c / s * X + (k - 1) / s = Y := by
  rw [← h]; field_simp; ring

lemma core_aux4 {c s k : ℝ} (hc : c ≠ 0) (hs : s ≠ 0) :
    -c / s * ((k - 1) / c) + (k - 1) / s = 0 := by
  field_simp; ring

section Core

variable (hK : IsInjectiveCap K) (hφ0 : 0 < φ) (hφ1 : φ < π / 4)
include hK hφ0 hφ1

omit hφ1 in
lemma IsInjectiveCap.core_corner_right {t : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) :
    coreX K t * cos φ + coreY K t * sin φ ≤ supportFn K φ - 1 := by
  rw [← inner_innerCorner_eq_coords]
  exact hK.inner_innerCorner_u_le_right hφ0 ht.1 (by linarith [ht.2, pi_pos])

lemma IsInjectiveCap.core_corner_left {t : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) :
    -(coreX K t * cos φ) + coreY K t * sin φ ≤ supportFn K (π - φ) - 1 := by
  have := hK.inner_innerCorner_u_le_left hφ0 (by linarith [pi_pos]) (by linarith [ht.1]) ht.2
  rw [inner_innerCorner_eq_coords, cos_pi_sub, sin_pi_sub] at this
  linarith

lemma IsInjectiveCap.core_graph :
    StrictAntiOn (coreX K) (Icc φ (π / 2 - φ)) ∧
    coreX K '' Icc φ (π / 2 - φ) = Icc (coreX K (π / 2 - φ)) (coreX K φ) ∧
    IntegrableOn (coreC φ K) (Icc (coreX K (π / 2 - φ)) (coreX K φ)) ∧
    (∫ ξ in (coreX K (π / 2 - φ))..(coreX K φ), coreC φ K ξ)
      = -∫ t in φ..(π / 2 - φ), coreY K t * coreX' K t :=
  hK.integral_core_graph hφ0 (by linarith [pi_pos]) (by linarith [pi_pos])

lemma IsInjectiveCap.coreC_of_mem {ξ : ℝ} (hξ : ξ ∈ Icc (coreX K (π / 2 - φ)) (coreX K φ)) :
    ∃ t ∈ Icc φ (π / 2 - φ), coreX K t = ξ ∧ coreC φ K ξ = coreY K t := by
  obtain ⟨hanti, himg, -, -⟩ := hK.core_graph hφ0 hφ1
  rw [← himg] at hξ
  obtain ⟨t, ht, rfl⟩ := hξ
  exact ⟨t, ht, rfl, by rw [coreC, hanti.injOn.leftInvOn_invFunOn ht]⟩

lemma IsInjectiveCap.coreC_at {t : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) :
    coreC φ K (coreX K t) = coreY K t := by
  obtain ⟨hanti, -, -, -⟩ := hK.core_graph hφ0 hφ1
  rw [coreC, hanti.injOn.leftInvOn_invFunOn ht]

lemma IsInjectiveCap.coreX_lt : coreX K (π / 2 - φ) < coreX K φ := by
  obtain ⟨hanti, -, -, -⟩ := hK.core_graph hφ0 hφ1
  have h : φ < π / 2 - φ := by linarith [pi_pos]
  exact hanti ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h

lemma IsInjectiveCap.core_roof :
    (∀ ξ ∈ Icc (coreX K (π / 2 - φ)) (coreX K φ), coreC φ K ξ ≤ coreD φ K ξ) ∧
    (∀ ξ ∈ Icc (coreX K (π / 2 - φ)) (coreX K φ), coreC φ K ξ ≤ coreB φ K ξ) ∧
    (∀ ξ, coreX K φ ≤ ξ → coreB φ K ξ ≤ coreD φ K ξ) ∧
    (∀ ξ, ξ ≤ coreX K (π / 2 - φ) → coreD φ K ξ ≤ coreB φ K ξ) := by
  have hpi := pi_pos
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hαβ : φ ≤ π / 2 - φ := by linarith
  have hcd : ∀ ξ ∈ Icc (coreX K (π / 2 - φ)) (coreX K φ), coreC φ K ξ ≤ coreD φ K ξ := by
    intro ξ hξ
    obtain ⟨t, ht, rfl, hct⟩ := hK.coreC_of_mem hφ0 hφ1 hξ
    rw [hct, coreD, le_div_iff₀ hs]
    linarith [hK.core_corner_left hφ0 hφ1 ht]
  have hcb : ∀ ξ ∈ Icc (coreX K (π / 2 - φ)) (coreX K φ), coreC φ K ξ ≤ coreB φ K ξ := by
    intro ξ hξ
    obtain ⟨t, ht, rfl, hct⟩ := hK.coreC_of_mem hφ0 hφ1 hξ
    rw [hct, coreB, le_div_iff₀ hs]
    linarith [hK.core_corner_right hφ0 ht]
  have hLR := hK.coreX_lt hφ0 hφ1
  refine ⟨hcd, hcb, fun ξ hξ => ?_, fun ξ hξ => ?_⟩
  · have h0 := hK.core_corner_left hφ0 hφ1 ⟨le_rfl, hαβ⟩
    have h1 := inner_innerCorner_u (S := K) φ
    rw [inner_innerCorner_eq_coords] at h1
    have h2 := mul_le_mul_of_nonneg_right hξ hc.le
    rw [coreB, coreD, div_le_div_iff_of_pos_right hs]
    linarith
  · have h0 := hK.core_corner_right hφ0 ⟨hαβ, le_rfl⟩
    have h1 := inner_innerCorner_u_add K (π / 2 - φ)
    rw [show π / 2 - φ + π / 2 = π - φ by ring, inner_innerCorner_eq_coords, cos_pi_sub,
      sin_pi_sub] at h1
    have h2 := mul_le_mul_of_nonneg_right hξ hc.le
    rw [coreB, coreD, div_le_div_iff_of_pos_right hs]
    linarith

omit hK in
/-- The pointwise containment behind Lemma 8.2.3. -/
lemma mem_core_region {q : ℝ²} (hq1 : 0 < q 1)
    (hR : q 0 * cos φ + q 1 * sin φ < supportFn K φ - 1)
    (hL : -(q 0 * cos φ) + q 1 * sin φ < supportFn K (π - φ) - 1)
    (hcase : (q 0 ≤ coreX K (π / 2 - φ) ∧ q 1 < coreY K (π / 2 - φ))
      ∨ (∃ t ∈ Icc φ (π / 2 - φ), coreX K t = q 0 ∧ q 1 < coreY K t)
      ∨ (coreX K φ ≤ q 0 ∧ q 1 < coreY K φ)) :
    q ∈ (niche K (π / 2) \ hpGe φ (supportFn K φ - 1)) \ hpGe (π - φ) (supportFn K (π - φ) - 1) := by
  have hpi := pi_pos
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hRq : ⟪q, u φ⟫ < supportFn K φ - 1 := by rw [inner_u_decomp]; exact hR
  have hLq : ⟪q, u (π - φ)⟫ < supportFn K (π - φ) - 1 := by
    rw [inner_u_decomp, cos_pi_sub, sin_pi_sub]; linarith
  have hfan : q ∈ fan (π / 2) :=
    ⟨hq1.le, by rw [inner_u_decomp, cos_pi_div_two, sin_pi_div_two]; linarith⟩
  have hQ : ∃ t ∈ Ioo (0 : ℝ) (π / 2), q ∈ QminusS K t := by
    rcases hcase with ⟨h1, h2⟩ | ⟨t, ht, hXt, h2⟩ | ⟨h1, h2⟩
    · refine ⟨π / 2 - φ, ⟨by linarith, by linarith⟩, ?_, ?_⟩
      · show ⟪q, u (π / 2 - φ)⟫ < supportFn K (π / 2 - φ) - 1
        have hx := inner_innerCorner_u (S := K) (π / 2 - φ)
        rw [inner_innerCorner_eq_coords, cos_pi_div_two_sub, sin_pi_div_two_sub] at hx
        rw [inner_u_decomp, cos_pi_div_two_sub, sin_pi_div_two_sub]
        have e1 := mul_le_mul_of_nonneg_right h1 hs.le
        have e2 := mul_lt_mul_of_pos_right h2 hc
        linarith
      · show ⟪q, u (π / 2 - φ + π / 2)⟫ < supportFn K (π / 2 - φ + π / 2) - 1
        rw [show π / 2 - φ + π / 2 = π - φ by ring]; exact hLq
    · have ht0 : 0 < t := by linarith [ht.1]
      have ht1 : t < π / 2 := by linarith [ht.2]
      have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 (by linarith)
      have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith, ht1⟩
      refine ⟨t, ⟨ht0, ht1⟩, ?_, ?_⟩
      · show ⟪q, u t⟫ < supportFn K t - 1
        have hx := inner_innerCorner_u (S := K) t
        rw [inner_innerCorner_eq_coords] at hx
        rw [inner_u_decomp, ← hXt]
        have e2 := mul_lt_mul_of_pos_right h2 hst
        linarith
      · show ⟪q, u (t + π / 2)⟫ < supportFn K (t + π / 2) - 1
        have hx := inner_innerCorner_u_add K t
        rw [inner_innerCorner_eq_coords, cos_add_pi_div_two, sin_add_pi_div_two] at hx
        rw [inner_u_decomp, cos_add_pi_div_two, sin_add_pi_div_two, ← hXt]
        have e2 := mul_lt_mul_of_pos_right h2 hct
        linarith
    · refine ⟨φ, ⟨hφ0, by linarith⟩, hRq, ?_⟩
      show ⟪q, u (φ + π / 2)⟫ < supportFn K (φ + π / 2) - 1
      have hx := inner_innerCorner_u_add K φ
      rw [inner_innerCorner_eq_coords, cos_add_pi_div_two, sin_add_pi_div_two] at hx
      rw [inner_u_decomp, cos_add_pi_div_two, sin_add_pi_div_two]
      have e1 := mul_le_mul_of_nonneg_right h1 hs.le
      have e2 := mul_lt_mul_of_pos_right h2 hc
      linarith
  obtain ⟨t, ht, hqt⟩ := hQ
  refine ⟨⟨mem_niche_iff.2 ⟨hfan, t, ht, hqt⟩, fun h => ?_⟩, fun h => ?_⟩
  · exact absurd (show supportFn K φ - 1 ≤ ⟪q, u φ⟫ from h) (not_le.2 hRq)
  · exact absurd (show supportFn K (π - φ) - 1 ≤ ⟪q, u (π - φ)⟫ from h) (not_le.2 hLq)

/-- The core region lies in `N(K) \ H̆^R_K \ H̆^L_K`. -/
lemma IsInjectiveCap.core_region_subset :
    {q : ℝ² | q 0 ∈ Ioo ((1 - supportFn K (π - φ)) / cos φ) ((supportFn K φ - 1) / cos φ)
        ∧ 0 < q 1 ∧ q 1 < coreU φ K (q 0)}
      ⊆ (niche K (π / 2) \ hpGe φ (supportFn K φ - 1))
          \ hpGe (π - φ) (supportFn K (π - φ) - 1) := by
  have hpi := pi_pos
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hαβ : φ ≤ π / 2 - φ := by linarith
  obtain ⟨hcd, hcb, hbd, hdb⟩ := hK.core_roof hφ0 hφ1
  have hLR := hK.coreX_lt hφ0 hφ1
  rintro q ⟨_, hq1, hqU⟩
  have hqd : q 1 < coreD φ K (q 0) := lt_of_lt_of_le hqU (coreRoof_le_d hLR hcd hbd _)
  have hqb : q 1 < coreB φ K (q 0) := lt_of_lt_of_le hqU (coreRoof_le_b hLR hcb hdb _)
  have hqd' := hqd
  have hqb' := hqb
  rw [coreD, lt_div_iff₀ hs] at hqd'
  rw [coreB, lt_div_iff₀ hs] at hqb'
  refine mem_core_region hφ0 hφ1 hq1 (by linarith) (by linarith) ?_
  by_cases h1 : q 0 ≤ coreX K (π / 2 - φ)
  · left
    refine ⟨h1, lt_of_lt_of_le hqd ?_⟩
    have hdL : coreD φ K (coreX K (π / 2 - φ)) = coreY K (π / 2 - φ) := by
      have h1 := inner_innerCorner_u_add K (π / 2 - φ)
      rw [show π / 2 - φ + π / 2 = π - φ by ring, inner_innerCorner_eq_coords, cos_pi_sub,
        sin_pi_sub] at h1
      rw [coreD, div_eq_iff hs.ne']; linarith
    rw [← hdL, coreD, coreD]
    exact div_le_div_of_nonneg_right (by linarith [mul_le_mul_of_nonneg_right h1 hc.le]) hs.le
  · by_cases h2 : q 0 < coreX K φ
    · right; left
      obtain ⟨t, ht, hXt, hct⟩ := hK.coreC_of_mem hφ0 hφ1 ⟨(not_le.1 h1).le, h2.le⟩
      refine ⟨t, ht, hXt, ?_⟩
      have hU : coreU φ K (q 0) = coreC φ K (q 0) := coreRoof_of_mem (not_le.1 h1) h2
      rw [hU, hct] at hqU
      exact hqU
    · right; right
      have h2' : coreX K φ ≤ q 0 := not_lt.1 h2
      refine ⟨h2', lt_of_lt_of_le hqb ?_⟩
      have hbR : coreB φ K (coreX K φ) = coreY K φ := by
        have h1 := inner_innerCorner_u (S := K) φ
        rw [inner_innerCorner_eq_coords] at h1
        rw [coreB, div_eq_iff hs.ne']; linarith
      rw [← hbR, coreB, coreB]
      exact div_le_div_of_nonneg_right (by linarith [mul_le_mul_of_nonneg_right h2' hc.le]) hs.le

/-- `J(W^R, x^R) + J(x_K) + J(x^L, Z^L) = ∫_Z^{ξ_L} d + ∫_{ξ_L}^{ξ_R} c + ∫_{ξ_R}^W b`. -/
lemma IsInjectiveCap.core_J_eq :
    segJ (ptWR φ K) (innerCorner K φ) + curveJ (innerCorner K) φ (π / 2 - φ)
        + segJ (innerCorner K (π / 2 - φ)) (ptZL φ K)
      = (∫ ξ in (1 - supportFn K (π - φ)) / cos φ..coreX K (π / 2 - φ), coreD φ K ξ)
        + (∫ ξ in coreX K (π / 2 - φ)..coreX K φ, coreC φ K ξ)
        + (∫ ξ in coreX K φ..(supportFn K φ - 1) / cos φ, coreB φ K ξ) := by
  have hpi := pi_pos
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hαβ : φ ≤ π / 2 - φ := by linarith
  obtain ⟨-, -, -, hcv⟩ := hK.core_graph hφ0 hφ1
  have hW0 : ⟪ptWR φ K, u 0⟫ = (supportFn K φ - 1) / cos φ := by
    rw [ptWR, real_inner_smul_left, inner_u_u, mul_one]
  have hZ0 : ⟪ptZL φ K, u 0⟫ = (1 - supportFn K (π - φ)) / cos φ := by
    rw [ptZL_eq_smul, real_inner_smul_left, inner_u_u, mul_one]
  have s1 : segJ (ptWR φ K) (innerCorner K φ)
      = (supportFn K φ - 1) / cos φ * coreY K φ / 2 := by
    rw [segJ, cross_eq_inner, hW0, inner_ptWR_u_pi_div_two, zero_mul, sub_zero]; rfl
  have s2 : segJ (innerCorner K (π / 2 - φ)) (ptZL φ K)
      = -((1 - supportFn K (π - φ)) / cos φ * coreY K (π / 2 - φ)) / 2 := by
    rw [segJ, cross_eq_inner, hZ0, inner_ptZL_u_pi_div_two, mul_zero, zero_sub]
    simp only [coreY]; ring
  have hdaff : coreD φ K = fun ξ => cos φ / sin φ * ξ + (supportFn K (π - φ) - 1) / sin φ := by
    funext ξ; rw [coreD]; ring
  have hbaff : coreB φ K = fun ξ => -cos φ / sin φ * ξ + (supportFn K φ - 1) / sin φ := by
    funext ξ; rw [coreB]; ring
  have i1 := integral_affine (cos φ / sin φ) ((supportFn K (π - φ) - 1) / sin φ)
    ((1 - supportFn K (π - φ)) / cos φ) (coreX K (π / 2 - φ))
  have i2 := integral_affine (-cos φ / sin φ) ((supportFn K φ - 1) / sin φ)
    (coreX K φ) ((supportFn K φ - 1) / cos φ)
  have hL := inner_innerCorner_u_add K (π / 2 - φ)
  rw [show π / 2 - φ + π / 2 = π - φ by ring, inner_innerCorner_eq_coords, cos_pi_sub,
    sin_pi_sub] at hL
  have hR := inner_innerCorner_u (S := K) φ
  rw [inner_innerCorner_eq_coords] at hR
  rw [core_aux1 hc.ne' hs.ne', core_aux2 hs.ne' hL] at i1
  rw [core_aux3 hs.ne' hR, core_aux4 hc.ne' hs.ne'] at i2
  rw [hdaff, hbaff, i1, i2, hcv, s1, s2, hK.curveJ_core hφ0 hαβ (by linarith)]
  ring

end Core

/-- **Baek Lemma 8.2.3** (without Green's theorem):
`J(W^R_K, x^R_K) + J(x_K|[φ^R, φ^L]) + J(x^L_K, Z^L_K) ≤ |N(K) \ H̆^R_K \ H̆^L_K|`. -/
theorem IsInjectiveCap.le_volumeReal_niche_core (hK : IsInjectiveCap K) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 4) (hsum : 2 ≤ supportFn K φ + supportFn K (π - φ))
    (hN : niche K (π / 2) ⊆ K) :
    segJ (ptWR φ K) (innerCorner K φ) + curveJ (innerCorner K) φ (π / 2 - φ)
        + segJ (innerCorner K (π / 2 - φ)) (ptZL φ K)
      ≤ volume.real ((niche K (π / 2) \ hpGe φ (supportFn K φ - 1))
          \ hpGe (π - φ) (supportFn K (π - φ) - 1)) := by
  have hpi := pi_pos
  have hKc := hK.isCap.isCompact
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  obtain ⟨-, -, hcint, -⟩ := hK.core_graph hφ0 hφ1
  obtain ⟨hcd, hcb, hbd, hdb⟩ := hK.core_roof hφ0 hφ1
  have hLR := hK.coreX_lt hφ0 hφ1
  have hZW : (1 - supportFn K (π - φ)) / cos φ ≤ (supportFn K φ - 1) / cos φ := by
    rw [div_le_div_iff_of_pos_right hc]; linarith
  have h1D := integral_pieces_le hLR hZW (continuous_coreD φ K) (continuous_coreB φ K) hcint
    hcd hcb hbd hdb
  have hUint : IntegrableOn (coreU φ K)
      (Ioo ((1 - supportFn K (π - φ)) / cos φ) ((supportFn K φ - 1) / cos φ)) :=
    (integrableOn_coreRoof hLR (continuous_coreD φ K) (continuous_coreB φ K) hcint _ _).mono_set
      Ioo_subset_Icc_self
  have hvol := volume_underGraph hUint
  have hsub := hK.core_region_subset hφ0 hφ1
  have hfinN : volume ((niche K (π / 2) \ hpGe φ (supportFn K φ - 1))
      \ hpGe (π - φ) (supportFn K (π - φ) - 1)) ≠ ⊤ :=
    measure_ne_top_of_subset ((sdiff_subset.trans sdiff_subset).trans hN) hKc.measure_lt_top.ne
  have hnn : 0 ≤ ∫ ξ in Ioo ((1 - supportFn K (π - φ)) / cos φ) ((supportFn K φ - 1) / cos φ),
      max (coreU φ K ξ) 0 :=
    integral_nonneg fun ξ => le_max_right _ _
  rw [hK.core_J_eq hφ0 hφ1]
  calc _ ≤ _ := h1D
    _ = volume.real {q : ℝ² | q 0 ∈ Ioo ((1 - supportFn K (π - φ)) / cos φ)
          ((supportFn K φ - 1) / cos φ) ∧ 0 < q 1 ∧ q 1 < coreU φ K (q 0)} := by
      rw [measureReal_def, hvol, ENNReal.toReal_ofReal hnn]; rfl
    _ ≤ _ := measureReal_mono hsub hfinN

/-! ## Theorem 8.2.4 -/

/-- **Baek Theorem 8.2.4**: `A(K) ≤ 𝒬(K, B_K, D_K)` for injective caps (with `N(K) ⊆ K` and the
width condition that replaces `|K| ≥ 2.2`). -/
theorem IsInjectiveCap.sofaArea_le_Qfun (hK : IsInjectiveCap K) (hφ0 : 0 < φ) (hφ1 : φ < π / 4)
    (hwid2 : 2 + 2 * sin φ < (supportFn K 0 + supportFn K π) * cos φ)
    (hN : niche K (π / 2) ⊆ K) :
    sofaArea K (π / 2) ≤ Qfun φ K (Bset φ K) (Dset φ K) := by
  have hpi := pi_pos
  have hcap := hK.isCap
  have hKc := hcap.isCompact
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ0 (by linarith)
  have hφ2 : φ < π / 2 := by linarith
  have hwid : 1 ≤ (supportFn K 0 + supportFn K π) * cos φ := by nlinarith
  have hA : supportFn K 0 * cos φ ≤ supportFn K φ := by
    have := hcap.inner_le hcap.cornerR_mem φ
    rwa [real_inner_smul_left, inner_u_u_eq_cos, zero_sub, cos_neg] at this
  have hC : supportFn K π * cos φ ≤ supportFn K (π - φ) := by
    have := hcap.inner_le hcap.cornerL_mem (π - φ)
    rwa [real_inner_smul_left, inner_u_u_eq_cos, show π - (π - φ) = φ by ring] at this
  have hsum : 2 ≤ supportFn K φ + supportFn K (π - φ) := by
    rw [add_mul] at hwid2; nlinarith
  have hL := hK.leq_Bset_Dset hφ0 hφ2 hwid hN
  have h1 := hK.le_volumeReal_niche_right hφ0 hφ2 hwid hN
  have h2 := hK.le_volumeReal_niche_left hφ0 hφ2 hwid hN
  have h3 := hK.le_volumeReal_niche_core hφ0 hφ1 hsum hN
  -- the three regions are disjoint pieces of `N(K)`
  set N := niche K (π / 2) with hNdef
  set R := hpGe φ (supportFn K φ - 1) with hRdef
  set L := hpGe (π - φ) (supportFn K (π - φ) - 1) with hLdef
  have hmR : MeasurableSet R := (isClosed_hpGe _ _).measurableSet
  have hmL : MeasurableSet L := (isClosed_hpGe _ _).measurableSet
  have hmN : MeasurableSet N := measurableSet_niche K (π / 2)
  have hfin : ∀ S ⊆ N, volume S ≠ ⊤ := fun S hS =>
    measure_ne_top_of_subset (hS.trans hN) hKc.measure_lt_top.ne
  have hdisj1 : Disjoint (N ∩ R) (N ∩ L) := by
    rw [Set.disjoint_left]
    rintro p ⟨hpN, hpR⟩ ⟨_, hpL⟩
    exact hcap.not_mem_right_left hφ0 hφ2 hwid2 (hN hpN) hpR hpL
  have hdisj2 : Disjoint ((N ∩ R) ∪ (N ∩ L)) ((N \ R) \ L) := by
    rw [Set.disjoint_left]
    rintro p (⟨_, hpR⟩ | ⟨_, hpL⟩) ⟨⟨_, hpR'⟩, hpL'⟩
    · exact hpR' hpR
    · exact hpL' hpL
  have hU1 := measureReal_union₀ (μ := volume) (hmN.inter hmL).nullMeasurableSet
    hdisj1.aedisjoint (hfin _ inter_subset_left) (hfin _ inter_subset_left)
  have hU2 := measureReal_union₀ (μ := volume) ((hmN.diff hmR).diff hmL).nullMeasurableSet
    hdisj2.aedisjoint (hfin _ (union_subset inter_subset_left inter_subset_left))
    (hfin _ (sdiff_subset.trans sdiff_subset))
  have hsubN : (N ∩ R) ∪ (N ∩ L) ∪ ((N \ R) \ L) ⊆ N :=
    union_subset (union_subset inter_subset_left inter_subset_left)
      (sdiff_subset.trans sdiff_subset)
  have hmono := measureReal_mono hsubN (hfin N le_rfl)
  rw [hU2, hU1] at hmono
  -- collinear chains
  have uπφ : ∀ p : ℝ², ⟪p, u (π + φ)⟫ = -⟪p, u φ⟫ := fun p => by
    rw [add_comm, u_add_pi, inner_neg_right]
  have u2πφ : ∀ p : ℝ², ⟪p, u (2 * π - φ)⟫ = -⟪p, u (π - φ)⟫ := fun p => by
    rw [show 2 * π - φ = (π - φ) + π by ring, u_add_pi, inner_neg_right]
  have hXB : ⟪vtxP (Bset φ K) (π + φ), u φ⟫ = supportFn K φ - 1 := by
    have h := inner_vtxP_u (Bset φ K) (π + φ)
    rw [uπφ] at h
    linarith [hL.B_phi]
  have hYD : ⟪vtxM (Dset φ K) (2 * π - φ), u (π - φ)⟫ = supportFn K (π - φ) - 1 := by
    have h := inner_vtxM_u (Dset φ K) (2 * π - φ)
    rw [u2πφ] at h
    linarith [hL.D_phi]
  have hxR : ⟪innerCorner K φ, u φ⟫ = supportFn K φ - 1 := inner_innerCorner_u φ
  have hxL : ⟪innerCorner K (π / 2 - φ), u (π - φ)⟫ = supportFn K (π - φ) - 1 := by
    have := inner_innerCorner_u_add K (π / 2 - φ)
    rwa [show π / 2 - φ + π / 2 = π - φ by ring] at this
  have hWR := inner_ptWR_u φ K hc.ne'
  have hZL := inner_ptZL_u φ K hc.ne'
  have cR : segJ (vtxP (Bset φ K) (π + φ)) (ptWR φ K) + segJ (ptWR φ K) (innerCorner K φ)
      = -segJ (innerCorner K φ) (vtxP (Bset φ K) (π + φ)) := by
    rw [segJ_on_line hXB hWR, segJ_on_line hWR hxR, segJ_on_line hxR hXB,
      inner_sub_left, inner_sub_left, inner_sub_left]; ring
  have cL : segJ (innerCorner K (π / 2 - φ)) (ptZL φ K)
        + segJ (ptZL φ K) (vtxM (Dset φ K) (2 * π - φ))
      = -segJ (vtxM (Dset φ K) (2 * π - φ)) (innerCorner K (π / 2 - φ)) := by
    rw [segJ_on_line hxL hZL, segJ_on_line hZL hYD, segJ_on_line hYD hxL,
      inner_sub_left, inner_sub_left, inner_sub_left]; ring
  rw [sofaArea, Qfun, ← measureReal_def, ← measureReal_def]
  linarith

/-! ## Balanced maximum caps, and the domain `𝓛` -/

/-- A cap of rotation angle `π/2` lies in `[−h(π), h(0)] × [0, 1]`, so `|K| ≤ h_K(0) + h_K(π)`. -/
lemma IsCap.volumeReal_le_width (hK : IsCap K (π / 2)) :
    volume.real K ≤ supportFn K 0 + supportFn K π := by
  let e : ℝ² ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e volume volume :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
      (volume_preserving_finTwoArrow ℝ)
  have hsub : K ⊆ e ⁻¹' (Icc (-supportFn K π) (supportFn K 0) ×ˢ Icc (0 : ℝ) 1) := by
    intro q hq
    have h0 := hK.inner_le hq 0
    have hπ := hK.inner_le hq π
    have h1 := hK.inner_le hq (π / 2)
    have h3 := hK.coord_one_nonneg hq
    rw [hK.supportFn_pi_div_two] at h1
    rw [inner_u_decomp, cos_zero, sin_zero] at h0
    rw [inner_u_decomp, cos_pi, sin_pi] at hπ
    rw [inner_u_decomp, cos_pi_div_two, sin_pi_div_two] at h1
    have e1 : (e q).1 = q 0 := rfl
    have e2 : (e q).2 = q 1 := rfl
    show (e q).1 ∈ Icc _ _ ∧ (e q).2 ∈ Icc _ _
    rw [e1, e2]
    exact ⟨⟨by linarith, by linarith⟩, ⟨h3, by linarith⟩⟩
  have hvol : volume (e ⁻¹' (Icc (-supportFn K π) (supportFn K 0) ×ˢ Icc (0 : ℝ) 1))
      = ENNReal.ofReal (supportFn K 0 + supportFn K π) := by
    rw [he.measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
      Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one, sub_neg_eq_add]
  have hnn : 0 ≤ supportFn K 0 + supportFn K π := by
    have := hK.inner_le hK.cornerL_mem 0
    rw [real_inner_smul_left, inner_u_u_eq_cos, sub_zero, cos_pi] at this
    linarith
  calc volume.real K
      ≤ volume.real (e ⁻¹' (Icc (-supportFn K π) (supportFn K 0) ×ˢ Icc (0 : ℝ) 1)) :=
        measureReal_mono hsub (by rw [hvol]; exact ENNReal.ofReal_ne_top)
    _ = _ := by rw [measureReal_def, hvol, ENNReal.toReal_ofReal hnn]

lemma sofaArea_le_volumeReal (K : Set ℝ²) (ω : ℝ) : sofaArea K ω ≤ volume.real K := by
  rw [sofaArea, measureReal_def]
  linarith [ENNReal.toReal_nonneg (a := volume (niche K ω))]

/-- For `0 < φ ≤ 1/25` and `h_K(0) + h_K(π) ≥ 2.2`: the width condition of Lemmas 8.1.4–8.1.5. -/
lemma width_of_area {w φ : ℝ} (hw : 11 / 5 ≤ w) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1 / 25) :
    2 + 2 * sin φ < w * cos φ := by
  have hs := Real.sin_le hφ0.le
  have hc := Real.one_sub_sq_div_two_le_cos (x := φ)
  have hφ2 : φ ^ 2 ≤ 1 / 625 := by nlinarith
  have hc' : 1249 / 1250 ≤ cos φ := by linarith
  nlinarith [mul_le_mul hw hc' (by norm_num) (by linarith)]

/-- **Baek Def 8.1.3**: the domain `𝓛` (with `K_i` = injective caps of area `≥ 2.2`). -/
structure InL (φ : ℝ) (K B D : Set ℝ²) : Prop where
  injective : IsInjectiveCap K
  area : 11 / 5 ≤ volume.real K
  B_compact : IsCompact B
  B_convex : Convex ℝ B
  B_nonempty : B.Nonempty
  D_compact : IsCompact D
  D_convex : Convex ℝ D
  D_nonempty : D.Nonempty
  B_subset : B ⊆ K
  D_subset : D ⊆ K
  B_le : ∀ t ∈ Icc φ (π / 2), supportFn K t + supportFn B (π + t) ≤ 1
  D_le : ∀ t ∈ Icc 0 (π / 2 - φ), supportFn K (π / 2 + t) + supportFn D (3 * π / 2 + t) ≤ 1
  eq : LEq φ K B D

/-- **Baek Theorem 8.1.8**: `(K, B_K, D_K) ∈ 𝓛` (for `N(K) ⊆ K`, which Baek's proof uses). -/
theorem IsInjectiveCap.inL (hK : IsInjectiveCap K) (hA : 11 / 5 ≤ volume.real K)
    (hφ0 : 0 < φ) (hφ1 : φ ≤ 1 / 25) (hN : niche K (π / 2) ⊆ K) :
    InL φ K (Bset φ K) (Dset φ K) := by
  have hpi := pi_gt_three
  have hcap := hK.isCap
  have hwid2 := width_of_area (hA.trans hcap.volumeReal_le_width) hφ0 hφ1
  have hwid : 1 ≤ (supportFn K 0 + supportFn K π) * cos φ := by
    have := sin_pos_of_pos_of_lt_pi hφ0 (by linarith); nlinarith
  exact
    { injective := hK
      area := hA
      B_compact := isCompact_Bset hcap.isCompact
      B_convex := convex_Bset hcap.convex
      B_nonempty := hcap.Bset_nonempty hφ0.le
      D_compact := isCompact_Dset hcap.isCompact
      D_convex := convex_Dset hcap.convex
      D_nonempty := hcap.Dset_nonempty hφ0.le
      B_subset := Bset_subset
      D_subset := Dset_subset
      B_le := fun t ht => hcap.supportFn_add_Bset_le hφ0.le ht
      D_le := fun t ht => hcap.supportFn_add_Dset_le hφ0.le ht
      eq := hK.leq_Bset_Dset hφ0 (by linarith) hwid hN }

/-- **Theorem 8.2.4 for balanced maximum caps**: `A(K) ≤ 𝒬(K, B_K, D_K)` for every
`φ ∈ (0, 1/25]`, as soon as `A(K) ≥ 2.2`. -/
theorem IsBalancedMaxCap.sofaArea_le_Qfun (hK : IsBalancedMaxCap K (π / 2))
    (hA : 11 / 5 ≤ sofaArea K (π / 2)) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1 / 25) :
    sofaArea K (π / 2) ≤ Qfun φ K (Bset φ K) (Dset φ K) := by
  have hpi := pi_gt_three
  have hinj := isInjectiveCap_of_balanced hK
  have hN := hK.niche_subset (by positivity) le_rfl
  have hw := (hA.trans (sofaArea_le_volumeReal K _)).trans hK.1.volumeReal_le_width
  exact hinj.sofaArea_le_Qfun hφ0 (by linarith) (width_of_area hw hφ0 hφ1) hN

/-- **Theorem 8.1.8 for balanced maximum caps.** -/
theorem IsBalancedMaxCap.inL (hK : IsBalancedMaxCap K (π / 2))
    (hA : 11 / 5 ≤ sofaArea K (π / 2)) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1 / 25) :
    InL φ K (Bset φ K) (Dset φ K) :=
  (isInjectiveCap_of_balanced hK).inL (hA.trans (sofaArea_le_volumeReal K _)) hφ0 hφ1
    (hK.niche_subset (by positivity) le_rfl)

end Sofa
