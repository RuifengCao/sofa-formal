/-
# Sofa/Mamikon.lean — Baek §7.4: Mamikon's theorem

Fix a convex body `K` and `a < b`.  A curve `z` with `z(t)` on the supporting line `l_K(t)` for
every `t` is `z(t) = h_K(t) u_t + w(t) v_t`; its *Mamikon region* is swept by the tangent segment
from `v⁺_K(t)` to `z(t) = v⁺_K(t) + α(t) v_t`, `α = w − e⁺_K`.  Baek's Def 7.4.2 measures it by
following its boundary,

    `M_K(a, b; z) = J(v⁺_K(a), z(a)) + J(z|[a,b]) + J(z(b), v⁻_K(b)) − J(u^{a,b}_K)`,

and **Mamikon's theorem** (Thm 7.4.1) says `M_K(a, b; z) = ½∫_a^b α(t)² dt`.

With the closed form of `J(u^{a,b}_K)` (`two_mul_convJ_eq`) the proof is short:
`2 J(z) = ∫ (h² + w² + h w' − w h')`, one integration by parts turns `∫ h w'` into
`[h w] − ∫ h' w`, and `h' = e⁺` a.e.; everything else cancels, leaving `∫ (w − e⁺)²`.
No Lebesgue–Stieltjes calculus for vector measures (Baek's Lemma 5.1.3) is needed.

Theorem 7.4.2 (convexity in `K`) follows because `α` is convex-linear in `K` (`edgeMax_mix`)
and `x ↦ x²` is convex.

STATUS: [PROOF-C-local] round 1 (2026-09-22, Opus 5.5).
-/
import Sofa.CurveArea

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace Interval

namespace Sofa

variable {K : Set ℝ²}

/-- **Def 7.4.2**: the area of the Mamikon region, by following its boundary. -/
def mamikonM (K : Set ℝ²) (a b : ℝ) (z : ℝ → ℝ²) : ℝ :=
  segJ (vtxP K a) (z a) + curveJ z a b + segJ (z b) (vtxM K b) - convJ K a b

/-- The curve on the supporting lines of `K` with `v_t`-coordinate `w(t)`. -/
def tanCurve (K : Set ℝ²) (w : ℝ → ℝ) (t : ℝ) : ℝ² := supportFn K t • u t + w t • v t

lemma inner_tanCurve_u (K : Set ℝ²) (w : ℝ → ℝ) (t : ℝ) : ⟪tanCurve K w t, u t⟫ = supportFn K t := by
  rw [tanCurve, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u, inner_v_u]
  ring

lemma inner_tanCurve_v (K : Set ℝ²) (w : ℝ → ℝ) (t : ℝ) : ⟪tanCurve K w t, v t⟫ = w t := by
  rw [tanCurve, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_v, inner_v_v]
  ring

/-- Every curve on the supporting lines is a `tanCurve`. -/
lemma eq_tanCurve {z : ℝ → ℝ²} {t : ℝ} (hz : ⟪z t, u t⟫ = supportFn K t) :
    z t = tanCurve K (fun s => ⟪z s, v s⟫) t := by
  rw [tanCurve, ← hz]; exact decomp_u_v t (z t)

/-- The derivative of a `tanCurve`, where `h_K` and `w` are differentiable. -/
theorem hasDerivAt_tanCurve (hK : IsCompact K) (hne : K.Nonempty) {w : ℝ → ℝ} {t w' : ℝ}
    (h0 : edgeLength K t = 0) (hw : HasDerivAt w w' t) :
    HasDerivAt (tanCurve K w)
      ((edgeMax K t - w t) • u t + (supportFn K t + w') • v t) t := by
  have hh := hasDerivAt_supportFn_of_edgeLength_eq_zero hK hne h0
  have h1 := hh.smul (hasDerivAt_u t)
  have h2 := hw.smul (hasDerivAt_v t)
  have h3 := h1.add h2
  have e : supportFn K t • v t + edgeMax K t • u t + (w t • -u t + w' • v t)
      = (edgeMax K t - w t) • u t + (supportFn K t + w') • v t := by
    rw [smul_neg, sub_smul, add_smul]; abel
  rw [e] at h3
  exact h3

/-- **Baek Theorem 7.4.1 (Mamikon's theorem)**: `M_K(a, b; z) = ½∫_a^b α(t)² dt`, where
`z(t) = v⁺_K(t) + α(t) v_t` lies on the supporting line `l_K(t)`. -/
theorem mamikonM_eq (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ} (hab : a < b)
    {w : ℝ → ℝ} (hw : AbsolutelyContinuousOnInterval w a b) :
    mamikonM K a b (tanCurve K w) = (∫ t in a..b, (w t - edgeMax K t) ^ 2) / 2 := by
  have hcount := (countable_edgeLength_ne_zero hK hne).ae_notMem volume
  -- the integrand of `J(z)` a.e.
  have hcross : ∀ᵐ t ∂volume, t ∈ Ι a b →
      cross (tanCurve K w t) (deriv (tanCurve K w) t)
        = supportFn K t ^ 2 + w t ^ 2 + supportFn K t * deriv w t - w t * edgeMax K t := by
    filter_upwards [hcount, hw.ae_differentiableAt] with t ht0 htw htab
    have h0 : edgeLength K t = 0 := by simpa using ht0
    have hd := hasDerivAt_tanCurve hK hne h0 (htw (uIoc_subset_uIcc htab)).hasDerivAt
    rw [hd.deriv, tanCurve, cross_frame]; ring
  have hJ : 2 * curveJ (tanCurve K w) a b
      = ∫ t in a..b, (supportFn K t ^ 2 + w t ^ 2 + supportFn K t * deriv w t
          - w t * edgeMax K t) := by
    rw [curveJ, intervalIntegral.integral_congr_ae hcross]; ring
  -- integration by parts: `∫ h w' = [h w] − ∫ e⁺ w`
  have hibp : ∫ t in a..b, supportFn K t * deriv w t
      = supportFn K b * w b - supportFn K a * w a - ∫ t in a..b, edgeMax K t * w t := by
    rw [(absolutelyContinuousOnInterval_supportFn hK hne a b).integral_mul_deriv_eq_deriv_mul hw]
    congr 1
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_deriv_supportFn hK hne] with t ht _
    rw [ht]
  -- the convex arc and the two segments
  have hconv := two_mul_convJ_eq hK hne hab
  have hs1 : 2 * segJ (vtxP K a) (tanCurve K w a) = supportFn K a * (w a - edgeMax K a) := by
    rw [segJ, vtxP, tanCurve, cross_frame]; ring
  have hs2 : 2 * segJ (tanCurve K w b) (vtxM K b) = supportFn K b * (edgeMin K b - w b) := by
    rw [segJ, vtxM, tanCurve, cross_frame]; ring
  -- integrability of the pieces
  have hwc : ContinuousOn w (uIcc a b) := hw.continuousOn
  have hhc := continuous_supportFn hK hne
  have i_h2 : IntervalIntegrable (fun t => supportFn K t ^ 2) volume a b :=
    (hhc.pow 2).intervalIntegrable a b
  have i_w2 : IntervalIntegrable (fun t => w t ^ 2) volume a b :=
    (hwc.pow 2).intervalIntegrable
  have i_hw' : IntervalIntegrable (fun t => supportFn K t * deriv w t) volume a b :=
    hw.intervalIntegrable_deriv.continuousOn_mul hhc.continuousOn
  have i_we : IntervalIntegrable (fun t => w t * edgeMax K t) volume a b :=
    (intervalIntegrable_edgeMax hK hne a b).continuousOn_mul hwc
  have i_e2 := intervalIntegrable_edgeMax_sq hK hne a b
  -- split the integrals
  have sJ : ∫ t in a..b, (supportFn K t ^ 2 + w t ^ 2 + supportFn K t * deriv w t
        - w t * edgeMax K t)
      = (∫ t in a..b, supportFn K t ^ 2) + (∫ t in a..b, w t ^ 2)
        + (∫ t in a..b, supportFn K t * deriv w t) - ∫ t in a..b, w t * edgeMax K t := by
    rw [intervalIntegral.integral_sub ((i_h2.add i_w2).add i_hw') i_we,
      intervalIntegral.integral_add (i_h2.add i_w2) i_hw', intervalIntegral.integral_add i_h2 i_w2]
  have sC : ∫ t in a..b, (supportFn K t ^ 2 - edgeMax K t ^ 2)
      = (∫ t in a..b, supportFn K t ^ 2) - ∫ t in a..b, edgeMax K t ^ 2 :=
    intervalIntegral.integral_sub i_h2 i_e2
  have sM : ∫ t in a..b, (w t - edgeMax K t) ^ 2
      = (∫ t in a..b, w t ^ 2) - 2 * (∫ t in a..b, w t * edgeMax K t)
        + ∫ t in a..b, edgeMax K t ^ 2 := by
    have e : (fun t => (w t - edgeMax K t) ^ 2)
        = fun t => w t ^ 2 - 2 * (w t * edgeMax K t) + edgeMax K t ^ 2 := by
      funext t; ring
    rw [e, intervalIntegral.integral_add (i_w2.sub (i_we.const_mul 2)) i_e2,
      intervalIntegral.integral_sub i_w2 (i_we.const_mul 2), intervalIntegral.integral_const_mul]
  have sew : ∫ t in a..b, edgeMax K t * w t = ∫ t in a..b, w t * edgeMax K t := by
    congr 1; funext t; ring
  -- assemble
  have hM : 2 * mamikonM K a b (tanCurve K w)
      = 2 * segJ (vtxP K a) (tanCurve K w a) + 2 * curveJ (tanCurve K w) a b
        + 2 * segJ (tanCurve K w b) (vtxM K b) - 2 * convJ K a b := by
    rw [mamikonM]; ring
  have : 2 * mamikonM K a b (tanCurve K w) = ∫ t in a..b, (w t - edgeMax K t) ^ 2 := by
    rw [hM, hs1, hJ, hs2, hconv, sJ, hibp, sC, sM, sew]; ring
  linarith

/-- `M_K(a, b; z)` only depends on `z` on `[a, b]`. -/
theorem mamikonM_congr {z z' : ℝ → ℝ²} {a b : ℝ} (hab : a ≤ b) (h : EqOn z z' (Icc a b)) :
    mamikonM K a b z = mamikonM K a b z' := by
  rw [mamikonM, mamikonM, curveJ_congr hab h, h (left_mem_Icc.2 hab), h (right_mem_Icc.2 hab)]

/-- Mamikon's theorem for a curve given by its points: if `z(t) ∈ l_K(t)` for `t ∈ [a, b]` and
the `v_t`-coordinate of `z` is absolutely continuous on `[a, b]`, then
`M_K(a,b;z) = ½∫_a^b ⟪z(t) − v⁺_K(t), v_t⟫²`. -/
theorem mamikonM_eq' (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ} (hab : a < b)
    {z : ℝ → ℝ²} (hz : ∀ t ∈ Icc a b, ⟪z t, u t⟫ = supportFn K t)
    (hw : AbsolutelyContinuousOnInterval (fun t => ⟪z t, v t⟫) a b) :
    mamikonM K a b z = (∫ t in a..b, ⟪z t - vtxP K t, v t⟫ ^ 2) / 2 := by
  have hzeq : EqOn z (tanCurve K (fun s => ⟪z s, v s⟫)) (Icc a b) :=
    fun t ht => eq_tanCurve (hz t ht)
  rw [mamikonM_congr hab.le hzeq, mamikonM_eq hK hne hab hw]
  congr 2
  funext t
  rw [inner_sub_left, inner_vtxP_v]

/-! ## Theorem 7.4.2: the Mamikon area is convex in `K` -/

/-- **Baek Theorem 7.4.2** (convexity): if the curve `z_K` on the supporting lines of `K` is
convex-linear in `K` — here: its `v_t`-coordinate is `w_K`, and `w` of the Minkowski combination is
the combination of the `w`s — then `K ↦ M_K(a, b; z_K)` is convex along `c_λ`. -/
theorem mamikonM_mix_le {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {a b : ℝ} (hab : a < b)
    {wA wB : ℝ → ℝ} (hwA : AbsolutelyContinuousOnInterval wA a b)
    (hwB : AbsolutelyContinuousOnInterval wB a b) :
    mamikonM (mix l A B) a b (tanCurve (mix l A B) (fun t => (1 - l) * wA t + l * wB t))
      ≤ (1 - l) * mamikonM A a b (tanCurve A wA) + l * mamikonM B a b (tanCurve B wB) := by
  have hM := isCompact_mix (l := l) hA hB
  have hMne := nonempty_mix (l := l) hAne hBne
  have hw : AbsolutelyContinuousOnInterval (fun t => (1 - l) * wA t + l * wB t) a b :=
    (hwA.const_mul (1 - l)).add (hwB.const_mul l)
  rw [mamikonM_eq hM hMne hab hw, mamikonM_eq hA hAne hab hwA, mamikonM_eq hB hBne hab hwB]
  simp only [edgeMax_mix hA hAne hB hBne hl0 hl1]
  -- pointwise convexity of `x ↦ x²`
  have hpt : ∀ t, ((1 - l) * wA t + l * wB t - ((1 - l) * edgeMax A t + l * edgeMax B t)) ^ 2
      ≤ (1 - l) * (wA t - edgeMax A t) ^ 2 + l * (wB t - edgeMax B t) ^ 2 := by
    intro t
    have h := mul_nonneg (mul_nonneg hl0 (sub_nonneg.2 hl1))
      (sq_nonneg ((wA t - edgeMax A t) - (wB t - edgeMax B t)))
    nlinarith [h]
  have iA : IntervalIntegrable (fun t => (wA t - edgeMax A t) ^ 2) volume a b := by
    have e : (fun t => (wA t - edgeMax A t) ^ 2)
        = fun t => wA t ^ 2 - 2 * (wA t * edgeMax A t) + edgeMax A t ^ 2 := by funext t; ring
    rw [e]
    exact ((hwA.continuousOn.pow 2).intervalIntegrable.sub
      (((intervalIntegrable_edgeMax hA hAne a b).continuousOn_mul hwA.continuousOn).const_mul 2)).add
      (intervalIntegrable_edgeMax_sq hA hAne a b)
  have iB : IntervalIntegrable (fun t => (wB t - edgeMax B t) ^ 2) volume a b := by
    have e : (fun t => (wB t - edgeMax B t) ^ 2)
        = fun t => wB t ^ 2 - 2 * (wB t * edgeMax B t) + edgeMax B t ^ 2 := by funext t; ring
    rw [e]
    exact ((hwB.continuousOn.pow 2).intervalIntegrable.sub
      (((intervalIntegrable_edgeMax hB hBne a b).continuousOn_mul hwB.continuousOn).const_mul 2)).add
      (intervalIntegrable_edgeMax_sq hB hBne a b)
  have iM : IntervalIntegrable (fun t => ((1 - l) * wA t + l * wB t
      - ((1 - l) * edgeMax A t + l * edgeMax B t)) ^ 2) volume a b := by
    have e : (fun t => ((1 - l) * wA t + l * wB t - ((1 - l) * edgeMax A t + l * edgeMax B t)) ^ 2)
        = fun t => ((1 - l) * (wA t - edgeMax A t) + l * (wB t - edgeMax B t)) ^ 2 := by
      funext t; ring
    rw [e]
    have hc : ∀ t, ((1 - l) * (wA t - edgeMax A t) + l * (wB t - edgeMax B t)) ^ 2
        = (1 - l) ^ 2 * (wA t - edgeMax A t) ^ 2
          + 2 * ((1 - l) * l) * ((wA t - edgeMax A t) * (wB t - edgeMax B t))
          + l ^ 2 * (wB t - edgeMax B t) ^ 2 := fun t => by ring
    simp only [hc]
    have iAB : IntervalIntegrable
        (fun t => (wA t - edgeMax A t) * (wB t - edgeMax B t)) volume a b := by
      have e2 : (fun t => (wA t - edgeMax A t) * (wB t - edgeMax B t))
          = fun t => ((wA t - edgeMax A t + (wB t - edgeMax B t)) ^ 2
              - (wA t - edgeMax A t) ^ 2 - (wB t - edgeMax B t) ^ 2) / 2 := by
        funext t; ring
      rw [e2]
      refine ((IntervalIntegrable.sub ?_ iA).sub iB).div_const 2
      have e3 : (fun t => (wA t - edgeMax A t + (wB t - edgeMax B t)) ^ 2)
          = fun t => ((wA t + wB t) - (edgeMax A t + edgeMax B t)) ^ 2 := by funext t; ring
      rw [e3]
      have e4 : (fun t => ((wA t + wB t) - (edgeMax A t + edgeMax B t)) ^ 2)
          = fun t => (wA t + wB t) ^ 2 - 2 * ((wA t + wB t) * (edgeMax A t + edgeMax B t))
              + (edgeMax A t + edgeMax B t) ^ 2 := by funext t; ring
      rw [e4]
      have hsum : ContinuousOn (fun t => wA t + wB t) (uIcc a b) :=
        hwA.continuousOn.add hwB.continuousOn
      have ie : IntervalIntegrable (fun t => edgeMax A t + edgeMax B t) volume a b :=
        (intervalIntegrable_edgeMax hA hAne a b).add (intervalIntegrable_edgeMax hB hBne a b)
      have ie2 : IntervalIntegrable (fun t => (edgeMax A t + edgeMax B t) ^ 2) volume a b := by
        obtain ⟨RA, _, hRA⟩ := exists_radius hA hAne
        obtain ⟨RB, _, hRB⟩ := exists_radius hB hBne
        refine intervalIntegrable_of_bdd
          (((measurable_edgeMax hA hAne).add (measurable_edgeMax hB hBne)).pow_const 2)
          (C := (RA + RB) ^ 2) (fun t => ?_) a b
        rw [abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        exact (abs_add_le _ _).trans (add_le_add (abs_edgeMax_le hA hAne hRA t)
          (abs_edgeMax_le hB hBne hRB t))
      exact ((hsum.pow 2).intervalIntegrable.sub ((ie.continuousOn_mul hsum).const_mul 2)).add ie2
    exact ((iA.const_mul _).add (iAB.const_mul _)).add (iB.const_mul _)
  have hmono := intervalIntegral.integral_mono_on hab.le iM
    ((iA.const_mul (1 - l)).add (iB.const_mul l)) (fun t _ => hpt t)
  rw [intervalIntegral.integral_add (iA.const_mul (1 - l)) (iB.const_mul l),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  linarith

end Sofa
