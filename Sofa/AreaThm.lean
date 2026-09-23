/-
# Sofa/AreaThm.lean — Baek Theorem 7.1.3: `|K| = ½ ∫ h_K dσ_K`

Step 5 of the route in `blueprint/ch3-8.md` §15.4–§15.5.  Steps 1–4 (`Sofa/Triangle.lean`,
`Sofa/SectorArea.lean`) give, for `A = v⁺_K(a)`, `B = v⁺_K(b)` and `sector K A B = K ∩ wedgeC A B`:

* additivity of `|sector K A ·|` (`volume_sector_add`);
* `½(A × B) ≤ |sector K A B| ≤ ½ λ² (A × B)` with `λ = h_K(b)/(h_K(b) − ⟪B−A, u_b⟫)`;
* `|A × B − σ_K((a,b]) h_K(b)| ≤ 2(b−a) σ (2R + σ)`;
* nondegeneracy of the wedge for a small enough mesh.

Here we put them together: on a short interval `|sector K A_a A_b| = ½ ∫_{(a,b]} h_K dσ_K`.

STATUS: in progress (2026-09-18, Opus 5).
-/
import Sofa.SectorArea

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²}

/-! ## The two quantities -/

/-- The area of the sector of `K` between the normal angles `a` and `b`. -/
def secR (K : Set ℝ²) (a b : ℝ) : ℝ := volume.real (sector K (vtxP K a) (vtxP K b))

/-- `½ ∫_{(a,b]} h_K dσ_K`. -/
def curveG (K : Set ℝ²) (a b : ℝ) : ℝ := (∫ t in Ioc a b, supportFn K t ∂(sigmaK K)) / 2

/-! ## Basic properties of `curveG` -/

lemma integrableOn_supportFn_sigmaK (hK : IsCompact K) (hne : K.Nonempty) (a b : ℝ) :
    IntegrableOn (supportFn K) (Ioc a b) (sigmaK K) :=
  (ContinuousOn.integrableOn_compact isCompact_Icc
    ((continuous_supportFn hK hne).continuousOn)).mono_set Ioc_subset_Icc_self

theorem curveG_add (hK : IsCompact K) (hne : K.Nonempty) {a b c : ℝ} (hab : a ≤ b)
    (hbc : b ≤ c) : curveG K a c = curveG K a b + curveG K b c := by
  have hdisj : Disjoint (Ioc a b) (Ioc b c) :=
    Set.disjoint_left.2 fun x hx hx' => absurd hx'.1 (not_lt.2 hx.2)
  rw [curveG, curveG, curveG, ← Set.Ioc_union_Ioc_eq_Ioc hab hbc,
    setIntegral_union hdisj measurableSet_Ioc (integrableOn_supportFn_sigmaK hK hne a b)
      (integrableOn_supportFn_sigmaK hK hne b c)]
  ring

/-- `∫_{(a,b]} h_K dσ_K` is `σ_K((a,b]) h_K(b)` up to `R (b−a) σ_K((a,b])`. -/
theorem abs_curveG_sub_le (hK : IsCompact K) (hne : K.Nonempty) {R : ℝ}
    (hR : ∀ p ∈ K, ‖p‖ ≤ R) {a b : ℝ} (hab : a ≤ b) :
    |2 * curveG K a b - (arcFn K b - arcFn K a) * supportFn K b|
      ≤ R * (b - a) * (arcFn K b - arcFn K a) := by
  have hmass : (sigmaK K (Ioc a b)).toReal = arcFn K b - arcFn K a :=
    sigmaK_Ioc_toReal hK hne hab
  have hfin : sigmaK K (Ioc a b) < ⊤ := lt_top_iff_ne_top.2 (sigmaK_Ioc_ne_top hK hne a b)
  have hconst : (∫ _t in Ioc a b, supportFn K b ∂(sigmaK K))
      = (arcFn K b - arcFn K a) * supportFn K b := by
    rw [setIntegral_const, smul_eq_mul, Measure.real, hmass]
  have hsub : (∫ t in Ioc a b, (supportFn K t - supportFn K b) ∂(sigmaK K))
      = (∫ t in Ioc a b, supportFn K t ∂(sigmaK K))
        - ∫ _t in Ioc a b, supportFn K b ∂(sigmaK K) :=
    integral_sub (integrableOn_supportFn_sigmaK hK hne a b)
      (integrableOn_const_sigmaK K (supportFn K b) a b)
  have hbd : |∫ t in Ioc a b, (supportFn K t - supportFn K b) ∂(sigmaK K)|
      ≤ R * (b - a) * (arcFn K b - arcFn K a) := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := sigmaK K) (s := Ioc a b)
      (f := fun t => supportFn K t - supportFn K b) (C := R * (b - a)) hfin ?_
    · rw [Real.norm_eq_abs, Measure.real, hmass] at h
      exact h
    · intro t ht
      rw [Real.norm_eq_abs]
      refine le_trans (abs_supportFn_sub_le hK hne hR t b) ?_
      have h1 : |t - b| ≤ b - a := by
        rw [abs_of_nonpos (by linarith [ht.2])]
        linarith [ht.1]
      have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR _ hne.some_mem)
      exact mul_le_mul_of_nonneg_left h1 hR0
  have he : 2 * curveG K a b = ∫ t in Ioc a b, supportFn K t ∂(sigmaK K) := by
    rw [curveG]; ring
  rw [he, ← hconst, ← hsub]
  exact hbd

/-! ## Basic properties of `secR` -/

lemma volume_sector_ne_top (hK : IsCompact K) (A B : ℝ²) : volume (sector K A B) ≠ ⊤ :=
  ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono Set.inter_subset_left)

lemma secR_nonneg (K : Set ℝ²) (a b : ℝ) : 0 ≤ secR K a b := measureReal_nonneg

/-- Real-valued additivity of the sector areas. -/
theorem secR_add (hK : IsCompact K) {a b c : ℝ} (hB : vtxP K b ≠ 0)
    (hAB : 0 ≤ cross (vtxP K a) (vtxP K b)) (hBC : 0 ≤ cross (vtxP K b) (vtxP K c))
    (hAC : 0 < cross (vtxP K a) (vtxP K c)) :
    secR K a c = secR K a b + secR K b c := by
  have h := volume_sector_add hK.isClosed.measurableSet hB hAB hBC hAC
  rw [secR, secR, secR, measureReal_def, measureReal_def, measureReal_def, h,
    ENNReal.toReal_add (volume_sector_ne_top hK _ _) (volume_sector_ne_top hK _ _)]

/-! ## The standing hypotheses -/

/-- The standing hypotheses for Thm 7.1.3: `K` is a convex body with `0` in its interior
(quantified by `hm ≤ h_K`) and radius at most `R`. -/
structure AreaSetup (K : Set ℝ²) (hm R : ℝ) : Prop where
  isCompact : IsCompact K
  nonempty : K.Nonempty
  convex : Convex ℝ K
  zero_mem : (0 : ℝ²) ∈ K
  hm_pos : 0 < hm
  hm_le : ∀ t : ℝ, hm ≤ supportFn K t
  norm_le : ∀ p ∈ K, ‖p‖ ≤ R

variable {hm R : ℝ}

lemma AreaSetup.R_nonneg (h : AreaSetup K hm R) : 0 ≤ R :=
  le_trans (norm_nonneg _) (h.norm_le _ h.nonempty.some_mem)

lemma AreaSetup.vtxP_ne_zero (h : AreaSetup K hm R) (t : ℝ) : vtxP K t ≠ 0 := by
  intro h0
  have hv := inner_vtxP_u K t
  rw [h0, inner_zero_left] at hv
  linarith [h.hm_le t, h.hm_pos]

lemma AreaSetup.supportFn_le (h : AreaSetup K hm R) (t : ℝ) : supportFn K t ≤ R := by
  rw [← inner_vtxP_u K t]
  refine le_trans (real_inner_le_norm _ _) ?_
  rw [norm_u, mul_one]
  exact h.norm_le _ (vtxP_mem h.isCompact h.nonempty t)

/-! ## The degenerate case -/

theorem secR_eq_zero_of_arcFn_eq (h : AreaSetup K hm R) {a b : ℝ} (hab : a ≤ b)
    (hδ : b - a < π / 2) (heq : arcFn K a = arcFn K b) : secR K a b = 0 := by
  have hv : vtxP K a = vtxP K b :=
    vtxP_eq_of_arcFn_eq h.isCompact h.nonempty hab hδ heq
  have hnull : volume (sector K (vtxP K a) (vtxP K b)) = 0 := by
    refine measure_mono_null (fun q hq => ?_)
      (volume_setOf_cross_eq_zero (h.vtxP_ne_zero a))
    have h1 := hq.2.1
    have h2 := hq.2.2
    rw [← hv] at h2
    exact le_antisymm h2 h1
  rw [secR, measureReal_def, hnull, ENNReal.toReal_zero]

theorem curveG_eq_zero_of_arcFn_eq (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ}
    (_hab : a ≤ b) (heq : arcFn K a = arcFn K b) : curveG K a b = 0 := by
  have hmass : sigmaK K (Ioc a b) = 0 := by
    rw [sigmaK_Ioc hK hne, heq, sub_self, ENNReal.ofReal_zero]
  rw [curveG, Measure.restrict_eq_zero.2 hmass, integral_zero_measure, zero_div]

/-! ## The arithmetic core of the local estimate -/

set_option maxHeartbeats 1000000 in
/-- Pure real-number bookkeeping behind `abs_secR_sub_curveG_le`. -/
lemma area_local_arith {δ σ β pp qq cc Av secr curg Sg M C hmv Rv : ℝ}
    (hm0 : 0 < hmv) (hR0 : 0 ≤ Rv) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hσ0 : 0 < σ) (hσS : σ ≤ Sg) (hM1 : 1 ≤ M) (hMR : Rv ≤ M) (hMS : Sg ≤ M)
    (hC : 71 * M ^ 3 ≤ hmv ^ 2 * (2 * C))
    (hsmall : 16 * δ * (Rv + Sg + 1) ≤ hmv)
    (hp0 : 0 ≤ pp) (hq0 : 0 ≤ qq) (_hqσ : qq ≤ σ) (hqhalf : σ / 2 ≤ qq)
    (hp2 : pp ≤ 2 * δ * σ)
    (hβm : hmv ≤ β) (hβR : β ≤ Rv) (hAvR : |Av| ≤ Rv)
    (hcc : cc = -(pp * Av) + qq * (β - pp))
    (hlow : cc ≤ 2 * secr) (hhigh : 2 * secr * (β - pp) ^ 2 ≤ β ^ 2 * cc)
    (hE2 : |cc - σ * β| ≤ 2 * δ * σ * (2 * Rv + σ))
    (hE3 : |σ * β - 2 * curg| ≤ Rv * δ * σ) :
    |secr - curg| ≤ C * δ * σ := by
  have hAv := abs_le.1 hAvR
  have hSg0 : 0 ≤ Sg := le_trans hσ0.le hσS
  have hδRn : (0:ℝ) ≤ δ * Rv := mul_nonneg hδ0 hR0
  have hδSn : (0:ℝ) ≤ δ * Sg := mul_nonneg hδ0 hSg0
  have hδSg : 16 * δ * Sg ≤ hmv := by linarith only [hsmall, hδ0, hδRn]
  have hδR : 16 * δ * Rv ≤ hmv := by linarith only [hsmall, hδ0, hδSn]
  have hppsmall : pp * Rv ≤ σ * hmv / 8 := by
    have h1 := mul_le_mul_of_nonneg_right hp2 hR0
    have h2 := mul_le_mul_of_nonneg_left hδR hσ0.le
    linarith only [h1, h2]
  have hpm : pp ≤ hmv / 8 := by
    have h1 : 2 * δ * σ ≤ 2 * δ * Sg :=
      mul_le_mul_of_nonneg_left hσS (by linarith only [hδ0])
    linarith only [hp2, h1, hδSg]
  have hβp : hmv / 2 ≤ β - pp := by linarith only [hβm, hpm, hm0]
  have hβp0 : 0 < β - pp := by linarith only [hβp, hm0]
  -- `cc` is positive and bounded above
  have hcc0 : 0 < cc := by
    have h1 : pp * Av ≤ pp * Rv := mul_le_mul_of_nonneg_left hAv.2 hp0
    have h2 : σ / 2 * (hmv / 2) ≤ qq * (β - pp) :=
      mul_le_mul hqhalf hβp (by linarith only [hm0]) hq0
    have h3 : 0 < σ * hmv := mul_pos hσ0 hm0
    rw [hcc]
    linarith only [h1, hppsmall, h2, h3]
  have hccub : cc ≤ σ * (3 * Rv + Sg) := by
    have hE2' := (abs_le.1 hE2).2
    have h1 : σ * β ≤ σ * Rv := mul_le_mul_of_nonneg_left hβR hσ0.le
    have k1 : 0 ≤ (1 - 2 * δ) * (σ * Rv) :=
      mul_nonneg (by linarith only [hδ]) (mul_nonneg hσ0.le hR0)
    have k2 : 0 ≤ (1 - 2 * δ) * (σ * σ) :=
      mul_nonneg (by linarith only [hδ]) (mul_nonneg hσ0.le hσ0.le)
    have k3 : σ * σ ≤ σ * Sg := mul_le_mul_of_nonneg_left hσS hσ0.le
    linarith only [hE2', h1, k1, k2, k3]
  -- the squeeze, in multiplied form
  have hd0 : 0 ≤ 2 * secr - cc := by linarith only [hlow]
  have hstep : (2 * secr - cc) * (β - pp) ^ 2 ≤ cc * (pp * (2 * β - pp)) := by
    linarith only [hhigh]
  have hstep2 : (2 * secr - cc) * (hmv / 2) ^ 2 ≤ cc * (pp * (2 * β - pp)) := by
    refine le_trans ?_ hstep
    have hsq : (hmv / 2) ^ 2 ≤ (β - pp) ^ 2 := by
      nlinarith only [mul_nonneg (by linarith only [hβp] : (0:ℝ) ≤ β - pp - hmv / 2)
        (by linarith only [hβp, hm0] : (0:ℝ) ≤ β - pp + hmv / 2)]
    exact mul_le_mul_of_nonneg_left hsq hd0
  -- bound the right-hand side
  have h2βn : 0 ≤ 2 * β - pp := by linarith only [hβm, hpm, hm0]
  have h2βb : 2 * β - pp ≤ 2 * Rv := by linarith only [hβR, hp0]
  have h1 : pp * (2 * β - pp) ≤ 4 * δ * σ * Rv := by
    have := mul_le_mul hp2 h2βb h2βn
      (mul_nonneg (mul_nonneg (by norm_num) hδ0) hσ0.le)
    linarith only [this]
  have h2 : 0 ≤ pp * (2 * β - pp) := mul_nonneg hp0 h2βn
  have hprod : cc * (pp * (2 * β - pp)) ≤ 4 * δ * σ * (Sg * (Rv * (3 * Rv + Sg))) := by
    have hccn : 0 ≤ σ * (3 * Rv + Sg) := mul_nonneg hσ0.le (by linarith only [hR0, hSg0])
    have hA : cc * (pp * (2 * β - pp)) ≤ (σ * (3 * Rv + Sg)) * (4 * δ * σ * Rv) :=
      mul_le_mul hccub h1 h2 hccn
    have hB : σ * (Rv * (3 * Rv + Sg)) ≤ Sg * (Rv * (3 * Rv + Sg)) :=
      mul_le_mul_of_nonneg_right hσS (mul_nonneg hR0 (by linarith only [hR0, hSg0]))
    have hC4 : (0:ℝ) ≤ 4 * δ * σ :=
      mul_nonneg (mul_nonneg (by norm_num) hδ0) hσ0.le
    have hD := mul_le_mul_of_nonneg_left hB hC4
    linarith only [hA, hD]
  have hMbound : Sg * (Rv * (3 * Rv + Sg)) ≤ 4 * M ^ 3 := by
    have j1 : Rv * (3 * Rv + Sg) ≤ M * (4 * M) :=
      mul_le_mul hMR (by linarith only [hMR, hMS]) (by linarith only [hR0, hSg0])
        (by linarith only [hMR, hR0])
    have j2 : Sg * (Rv * (3 * Rv + Sg)) ≤ M * (M * (4 * M)) :=
      mul_le_mul hMS j1 (mul_nonneg hR0 (by linarith only [hR0, hSg0]))
        (by linarith only [hM1])
    linarith only [j2]
  have hhm2 : hmv ^ 2 * (2 * secr - cc) ≤ 64 * δ * σ * M ^ 3 := by
    have hC4 : (0:ℝ) ≤ 4 * δ * σ := mul_nonneg (mul_nonneg (by norm_num) hδ0) hσ0.le
    have hE := mul_le_mul_of_nonneg_left hMbound hC4
    linarith only [hstep2, hprod, hE]
  -- the other two error terms
  have hhmM : hmv ≤ M := by linarith only [hβm, hβR, hMR]
  have hhm2M : hmv ^ 2 ≤ M ^ 2 := by
    nlinarith only [mul_nonneg (by linarith only [hhmM] : (0:ℝ) ≤ M - hmv)
      (by linarith only [hhmM, hm0] : (0:ℝ) ≤ M + hmv)]
  have hM0 : (0:ℝ) ≤ M := by linarith only [hM1]
  have hE2' : hmv ^ 2 * |cc - σ * β| ≤ 6 * δ * σ * M ^ 3 := by
    have hδσ : (0:ℝ) ≤ 2 * δ * σ := mul_nonneg (mul_nonneg (by norm_num) hδ0) hσ0.le
    have g1 : 2 * δ * σ * (2 * Rv + σ) ≤ 2 * δ * σ * (3 * M) :=
      mul_le_mul_of_nonneg_left (by linarith only [hMR, hσS, hMS]) hδσ
    have g2 : |cc - σ * β| ≤ 6 * δ * σ * M := by linarith only [hE2, g1]
    have g3 := mul_le_mul hhm2M g2 (abs_nonneg _) (by positivity)
    linarith only [g3]
  have hE3' : hmv ^ 2 * |σ * β - 2 * curg| ≤ 1 * δ * σ * M ^ 3 := by
    have g1 : Rv * δ * σ ≤ M * δ * σ := by
      nlinarith only [mul_nonneg (mul_nonneg (by linarith only [hMR] : (0:ℝ) ≤ M - Rv) hδ0)
        hσ0.le]
    have g2 : |σ * β - 2 * curg| ≤ M * δ * σ := by linarith only [hE3, g1]
    have g3 := mul_le_mul hhm2M g2 (abs_nonneg _) (by positivity)
    linarith only [g3]
  -- combine
  have htri : |2 * secr - 2 * curg|
      ≤ (2 * secr - cc) + |cc - σ * β| + |σ * β - 2 * curg| := by
    have e1 := abs_add_le ((2 * secr - cc) + (cc - σ * β)) (σ * β - 2 * curg)
    have e2 := abs_add_le (2 * secr - cc) (cc - σ * β)
    have e3 : |2 * secr - cc| = 2 * secr - cc := abs_of_nonneg hd0
    rw [show 2 * secr - 2 * curg
        = (2 * secr - cc) + (cc - σ * β) + (σ * β - 2 * curg) by ring]
    linarith only [e1, e2, e3]
  have hfin : hmv ^ 2 * |2 * secr - 2 * curg| ≤ 71 * δ * σ * M ^ 3 := by
    have h := mul_le_mul_of_nonneg_left htri (by positivity : (0:ℝ) ≤ hmv ^ 2)
    linarith only [h, hhm2, hE2', hE3']
  have habs2 : |2 * secr - 2 * curg| = 2 * |secr - curg| := by
    rw [show 2 * secr - 2 * curg = 2 * (secr - curg) by ring, abs_mul]
    norm_num
  rw [habs2] at hfin
  have hpos : (0:ℝ) < hmv ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hC (mul_nonneg hδ0 hσ0.le)
  have hle : hmv ^ 2 * (2 * |secr - curg|) ≤ hmv ^ 2 * (2 * (C * (δ * σ))) := by
    linarith only [hfin, hmul]
  have hres := le_of_mul_le_mul_left hle hpos
  linarith only [hres]

/-- The positivity part, extracted so that both the squeeze and the arithmetic core can use it. -/
lemma cross_pos_arith {δ σ β pp qq cc Av Sg hmv Rv : ℝ}
    (hm0 : 0 < hmv) (hR0 : 0 ≤ Rv) (hδ0 : 0 ≤ δ) (hσ0 : 0 < σ) (hσS : σ ≤ Sg)
    (hsmall : 16 * δ * (Rv + Sg + 1) ≤ hmv)
    (hp0 : 0 ≤ pp) (hq0 : 0 ≤ qq) (hqhalf : σ / 2 ≤ qq) (hp2 : pp ≤ 2 * δ * σ)
    (hβm : hmv ≤ β) (hAvR : |Av| ≤ Rv) (hcc : cc = -(pp * Av) + qq * (β - pp)) :
    pp ≤ hmv / 8 ∧ hmv / 2 ≤ β - pp ∧ 0 < cc := by
  have hAv := abs_le.1 hAvR
  have hSg0 : 0 ≤ Sg := le_trans hσ0.le hσS
  have hδRn : (0:ℝ) ≤ δ * Rv := mul_nonneg hδ0 hR0
  have hδSn : (0:ℝ) ≤ δ * Sg := mul_nonneg hδ0 hSg0
  have hδSg : 16 * δ * Sg ≤ hmv := by linarith only [hsmall, hδ0, hδRn]
  have hδR : 16 * δ * Rv ≤ hmv := by linarith only [hsmall, hδ0, hδSn]
  have hppsmall : pp * Rv ≤ σ * hmv / 8 := by
    have h1 := mul_le_mul_of_nonneg_right hp2 hR0
    have h2 := mul_le_mul_of_nonneg_left hδR hσ0.le
    linarith only [h1, h2]
  have hpm : pp ≤ hmv / 8 := by
    have h1 : 2 * δ * σ ≤ 2 * δ * Sg :=
      mul_le_mul_of_nonneg_left hσS (by linarith only [hδ0])
    linarith only [hp2, h1, hδSg]
  have hβp : hmv / 2 ≤ β - pp := by linarith only [hβm, hpm, hm0]
  refine ⟨hpm, hβp, ?_⟩
  have h1 : pp * Av ≤ pp * Rv := mul_le_mul_of_nonneg_left hAv.2 hp0
  have h2 : σ / 2 * (hmv / 2) ≤ qq * (β - pp) :=
    mul_le_mul hqhalf hβp (by linarith only [hm0]) hq0
  have h3 : 0 < σ * hmv := mul_pos hσ0 hm0
  rw [hcc]
  linarith only [h1, hppsmall, h2, h3]

/-! ## Local geometric facts -/

/-- The facts about `v⁺_K(a)`, `v⁺_K(b)` used repeatedly on a short interval. -/
lemma local_geom (h : AreaSetup K hm R) {a b : ℝ} (hab : a ≤ b) (hd : b - a ≤ 1 / 2) :
    (0 ≤ ⟪vtxP K b - vtxP K a, u b⟫)
    ∧ (0 ≤ ⟪vtxP K b - vtxP K a, v b⟫)
    ∧ (⟪vtxP K b - vtxP K a, v b⟫ ≤ arcFn K b - arcFn K a)
    ∧ ((arcFn K b - arcFn K a) / 2 ≤ ⟪vtxP K b - vtxP K a, v b⟫)
    ∧ (⟪vtxP K b - vtxP K a, u b⟫ ≤ 2 * (b - a) * (arcFn K b - arcFn K a))
    ∧ (|⟪vtxP K a, v b⟫| ≤ R)
    ∧ (cross (vtxP K a) (vtxP K b)
        = -(⟪vtxP K b - vtxP K a, u b⟫ * ⟪vtxP K a, v b⟫)
          + ⟪vtxP K b - vtxP K a, v b⟫
            * (supportFn K b - ⟪vtxP K b - vtxP K a, u b⟫)) := by
  have hKc := h.isCompact
  have hKne := h.nonempty
  have hδ0 : 0 ≤ b - a := by linarith
  have hσ0 : 0 ≤ arcFn K b - arcFn K a := by linarith [arcFn_mono hKc hKne hab]
  have hδπ : b - a < π / 2 := by linarith [pi_gt_three]
  have htan0 : 0 ≤ tan (b - a) :=
    tan_nonneg_of_nonneg_of_le_pi_div_two hδ0 (by linarith)
  have htan : tan (b - a) ≤ 2 * (b - a) := tan_le_two_mul hδ0 (by linarith)
  have hp0 : 0 ≤ ⟪vtxP K b - vtxP K a, u b⟫ := inner_vtxP_sub_u_nonneg hKc hKne a b
  have hq0 : 0 ≤ ⟪vtxP K b - vtxP K a, v b⟫ := inner_vtxP_sub_v_nonneg hKc hKne hab hδπ
  have hqσ : ⟪vtxP K b - vtxP K a, v b⟫ ≤ arcFn K b - arcFn K a :=
    inner_vtxP_sub_v_le_arcFn hKc hKne hab
  have hqhalf : (arcFn K b - arcFn K a) / 2 ≤ ⟪vtxP K b - vtxP K a, v b⟫ := by
    have hA := arcFn_sub_le hKc hKne hab hδπ
    have hB : (b - a) * (tan (b - a) * (arcFn K b - arcFn K a))
        ≤ (b - a) * (2 * (b - a) * (arcFn K b - arcFn K a)) := by
      refine mul_le_mul_of_nonneg_left ?_ hδ0
      exact mul_le_mul_of_nonneg_right htan hσ0
    have hD : (b - a) * (2 * (b - a) * (arcFn K b - arcFn K a))
        ≤ (arcFn K b - arcFn K a) / 2 := by
      have hq : (0:ℝ) ≤ 1 / 4 - (b - a) ^ 2 := by nlinarith only [hd, hδ0]
      nlinarith only [mul_nonneg hq hσ0]
    linarith only [hA, hB, hD]
  have hp2 : ⟪vtxP K b - vtxP K a, u b⟫ ≤ 2 * (b - a) * (arcFn K b - arcFn K a) := by
    have hA := inner_vtxP_sub_u_le_tan hKc hKne hab hδπ
    have hB : tan (b - a) * ⟪vtxP K b - vtxP K a, v b⟫
        ≤ tan (b - a) * (arcFn K b - arcFn K a) := mul_le_mul_of_nonneg_left hqσ htan0
    have hD : tan (b - a) * (arcFn K b - arcFn K a)
        ≤ 2 * (b - a) * (arcFn K b - arcFn K a) := mul_le_mul_of_nonneg_right htan hσ0
    linarith only [hA, hB, hD]
  have hAvR : |⟪vtxP K a, v b⟫| ≤ R := by
    refine le_trans ?_ (h.norm_le _ (vtxP_mem hKc hKne a))
    have hcs := abs_real_inner_le_norm (vtxP K a) (v b)
    rwa [norm_v, mul_one] at hcs
  have hAu : ⟪vtxP K a, u b⟫ = supportFn K b - ⟪vtxP K b - vtxP K a, u b⟫ := by
    rw [inner_sub_left, inner_vtxP_u]; ring
  have hcc : cross (vtxP K a) (vtxP K b)
      = -(⟪vtxP K b - vtxP K a, u b⟫ * ⟪vtxP K a, v b⟫)
        + ⟪vtxP K b - vtxP K a, v b⟫
          * (supportFn K b - ⟪vtxP K b - vtxP K a, u b⟫) := by
    rw [cross_eq_frame _ _ b, hAu]
  exact ⟨hp0, hq0, hqσ, hqhalf, hp2, hAvR, hcc⟩

/-- Strict positivity of the wedge, on a nondegenerate short interval. -/
theorem cross_vtxP_pos_of (h : AreaSetup K hm R) {Sg : ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : b - a ≤ 1 / 2) (hσS : arcFn K b - arcFn K a ≤ Sg)
    (hsmall : 16 * (b - a) * (R + Sg + 1) ≤ hm)
    (hpos : 0 < arcFn K b - arcFn K a) :
    0 < cross (vtxP K a) (vtxP K b) := by
  obtain ⟨hp0, hq0, -, hqhalf, hp2, hAvR, hcc⟩ := local_geom h hab hd
  exact (cross_pos_arith h.hm_pos h.R_nonneg (by linarith) hpos hσS hsmall hp0 hq0 hqhalf hp2
    (h.hm_le b) hAvR hcc).2.2

/-! ## The local estimate -/

set_option maxHeartbeats 1000000 in
/-- **Step 5(b)**: on a short interval, `|sector| = ½∫ h dσ` up to `C δ σ`. -/
theorem abs_secR_sub_curveG_le (h : AreaSetup K hm R) {Sg M C : ℝ}
    (hM1 : 1 ≤ M) (hMR : R ≤ M) (hMS : Sg ≤ M) (hC : 71 * M ^ 3 ≤ hm ^ 2 * (2 * C))
    {a b : ℝ} (hab : a ≤ b) (hδ : b - a ≤ 1 / 2)
    (hσS : arcFn K b - arcFn K a ≤ Sg)
    (hsmall : 16 * (b - a) * (R + Sg + 1) ≤ hm) :
    |secR K a b - curveG K a b| ≤ C * (b - a) * (arcFn K b - arcFn K a) := by
  have hm0 := h.hm_pos
  have hR0 := h.R_nonneg
  have hKc := h.isCompact
  have hKne := h.nonempty
  have hδ0 : 0 ≤ b - a := by linarith
  have hσ0 : 0 ≤ arcFn K b - arcFn K a := by linarith [arcFn_mono hKc hKne hab]
  have hδπ : b - a < π / 2 := by linarith [pi_gt_three]
  rcases eq_or_lt_of_le hσ0 with heq | hσpos
  · have harc : arcFn K a = arcFn K b := by linarith
    rw [secR_eq_zero_of_arcFn_eq h hab hδπ harc,
      curveG_eq_zero_of_arcFn_eq hKc hKne hab harc, ← heq]
    simp
  obtain ⟨hp0, hq0, hqσ, hqhalf, hp2, hAvR, hcc⟩ := local_geom h hab hδ
  have hAu : ⟪vtxP K a, u b⟫ = supportFn K b - ⟪vtxP K b - vtxP K a, u b⟫ := by
    rw [inner_sub_left, inner_vtxP_u]; ring
  have hβm : hm ≤ supportFn K b := h.hm_le b
  have hβR : supportFn K b ≤ R := h.supportFn_le b
  have hAvR : |⟪vtxP K a, v b⟫| ≤ R := by
    refine le_trans ?_ (h.norm_le _ (vtxP_mem hKc hKne a))
    have hcs := abs_real_inner_le_norm (vtxP K a) (v b)
    rwa [norm_v, mul_one] at hcs
  have hAu : ⟪vtxP K a, u b⟫ = supportFn K b - ⟪vtxP K b - vtxP K a, u b⟫ := by
    rw [inner_sub_left, inner_vtxP_u]; ring
  have hcc : cross (vtxP K a) (vtxP K b)
      = -(⟪vtxP K b - vtxP K a, u b⟫ * ⟪vtxP K a, v b⟫)
        + ⟪vtxP K b - vtxP K a, v b⟫ * (supportFn K b - ⟪vtxP K b - vtxP K a, u b⟫) := by
    rw [cross_eq_frame _ _ b, hAu]
  obtain ⟨hpm, hβp, hcc0⟩ := cross_pos_arith hm0 hR0 hδ0 hσpos hσS hsmall hp0 hq0 hqhalf hp2
    hβm hAvR hcc
  -- the squeeze
  have hsq := volume_sector_squeeze h.convex h.zero_mem (vtxP_mem hKc hKne a)
    (vtxP_mem hKc hKne b)
    (fun q hq => le_supportFn hKc hq b) (inner_vtxP_u K b) hAu
    (by linarith only [hβm, hm0]) hp0 (by linarith only [hpm, hβm, hm0]) hcc0
  have hnetop := volume_sector_ne_top hKc (vtxP K a) (vtxP K b)
  have hlow : cross (vtxP K a) (vtxP K b) ≤ 2 * secR K a b := by
    have := (ENNReal.ofReal_le_iff_le_toReal hnetop).1 hsq.1
    rw [secR, measureReal_def]
    linarith only [this]
  have hhigh : 2 * secR K a b * (supportFn K b - ⟪vtxP K b - vtxP K a, u b⟫) ^ 2
      ≤ supportFn K b ^ 2 * cross (vtxP K a) (vtxP K b) := by
    have hle := (ENNReal.le_ofReal_iff_toReal_le hnetop (by positivity)).1 hsq.2
    rw [secR, measureReal_def]
    have hne0 : supportFn K b - ⟪vtxP K b - vtxP K a, u b⟫ ≠ 0 := by
      intro h0; rw [h0] at hβp; linarith only [hβp, hm0]
    have hsqpos : (0:ℝ) < (supportFn K b - ⟪vtxP K b - vtxP K a, u b⟫) ^ 2 := by positivity
    have hstep := mul_le_mul_of_nonneg_right hle hsqpos.le
    have heq : (supportFn K b / (supportFn K b - ⟪vtxP K b - vtxP K a, u b⟫)) ^ 2
          * cross (vtxP K a) (vtxP K b) / 2
          * (supportFn K b - ⟪vtxP K b - vtxP K a, u b⟫) ^ 2
        = supportFn K b ^ 2 * cross (vtxP K a) (vtxP K b) / 2 := by
      field_simp
    rw [heq] at hstep
    linarith only [hstep]
  have hE2 := abs_cross_vtxP_sub_le hKc hKne hab (by linarith) h.norm_le
  have hE3 : |(arcFn K b - arcFn K a) * supportFn K b - 2 * curveG K a b|
      ≤ R * (b - a) * (arcFn K b - arcFn K a) := by
    rw [abs_sub_comm]
    exact abs_curveG_sub_le hKc hKne h.norm_le hab
  have hE2' : |cross (vtxP K a) (vtxP K b) - (arcFn K b - arcFn K a) * supportFn K b|
      ≤ 2 * (b - a) * (arcFn K b - arcFn K a) * (2 * R + (arcFn K b - arcFn K a)) := by
    refine le_trans hE2 ?_
    nlinarith only [hδ0, hσ0, hR0]
  exact area_local_arith hm0 hR0 hδ0 hδ hσpos hσS hM1 hMR hMS hC hsmall hp0 hq0 hqσ hqhalf hp2
    hβm hβR hAvR hcc hlow hhigh hE2' hE3

/-! ## Additivity, including the degenerate case -/

theorem secR_add' (h : AreaSetup K hm R) {Sg : ℝ} {x y z : ℝ}
    (hxy : x ≤ y) (hyz : y ≤ z) (hd : z - x ≤ 1 / 2)
    (hσS : arcFn K z - arcFn K x ≤ Sg)
    (hsmall : 16 * (z - x) * (R + Sg + 1) ≤ hm) :
    secR K x z = secR K x y + secR K y z := by
  have hKc := h.isCompact
  have hKne := h.nonempty
  have hR0 := h.R_nonneg
  have hxz : x ≤ z := le_trans hxy hyz
  have hmono1 := arcFn_mono hKc hKne hxy
  have hmono2 := arcFn_mono hKc hKne hyz
  have hσ0 : 0 ≤ arcFn K z - arcFn K x := by linarith
  have hSg0 : 0 ≤ Sg := le_trans hσ0 hσS
  rcases eq_or_lt_of_le hσ0 with heq | hpos
  · have h1 : arcFn K x = arcFn K y := by linarith
    have h2 : arcFn K y = arcFn K z := by linarith
    have h3 : arcFn K x = arcFn K z := by linarith
    rw [secR_eq_zero_of_arcFn_eq h hxz (by linarith [pi_gt_three]) h3,
      secR_eq_zero_of_arcFn_eq h hxy (by linarith [pi_gt_three]) h1,
      secR_eq_zero_of_arcFn_eq h hyz (by linarith [pi_gt_three]) h2]
    ring
  · have hAC : 0 < cross (vtxP K x) (vtxP K z) :=
      cross_vtxP_pos_of h hxz hd hσS hsmall hpos
    have key : ∀ s t : ℝ, x ≤ s → s ≤ t → t ≤ z →
        tan (t - s) * (R + (arcFn K t - arcFn K s)) ≤ hm := by
      intro s t hxs hst htz
      have hst0 : 0 ≤ t - s := by linarith
      have ht : tan (t - s) ≤ 2 * (t - s) := tan_le_two_mul hst0 (by linarith)
      have ht0 : 0 ≤ tan (t - s) :=
        tan_nonneg_of_nonneg_of_le_pi_div_two hst0 (by linarith [pi_gt_three])
      have hs1 : arcFn K t - arcFn K s ≤ Sg := by
        have := arcFn_mono hKc hKne hxs
        have := arcFn_mono hKc hKne htz
        linarith
      have hs2 : 0 ≤ arcFn K t - arcFn K s := by linarith [arcFn_mono hKc hKne hst]
      have hA : tan (t - s) * (R + (arcFn K t - arcFn K s)) ≤ 2 * (t - s) * (R + Sg) := by
        have hmm : tan (t - s) * (R + (arcFn K t - arcFn K s))
            ≤ (2 * (t - s)) * (R + Sg) :=
          mul_le_mul ht (by linarith) (by linarith) (by linarith)
        linarith
      have hB : 2 * (t - s) * (R + Sg) ≤ 2 * (z - x) * (R + Sg) := by
        have h2 : t - s ≤ z - x := by linarith
        nlinarith only [mul_le_mul_of_nonneg_right h2 (by linarith : (0:ℝ) ≤ R + Sg)]
      have hC2 : 2 * (z - x) * (R + Sg) ≤ hm := by
        have hz0 : 0 ≤ z - x := by linarith
        nlinarith only [hsmall, hz0, hR0, hSg0, mul_nonneg hz0 hR0, mul_nonneg hz0 hSg0]
      linarith
    have hAB : 0 ≤ cross (vtxP K x) (vtxP K y) :=
      cross_vtxP_nonneg hKc hKne hxy (by linarith [pi_gt_three]) h.norm_le h.hm_pos
        (h.hm_le y) (key x y le_rfl hxy hyz)
    have hBC : 0 ≤ cross (vtxP K y) (vtxP K z) :=
      cross_vtxP_nonneg hKc hKne hyz (by linarith [pi_gt_three]) h.norm_le h.hm_pos
        (h.hm_le z) (key y z hxy hyz le_rfl)
    exact secR_add hKc (h.vtxP_ne_zero y) hAB hBC hAC

/-! ## Step 5(c): the chaining -/

set_option maxHeartbeats 1000000 in
/-- **Baek Theorem 7.1.3, local form**: on a short interval of normal angles the sector area is
exactly `½ ∫ h_K dσ_K`. -/
theorem secR_eq_curveG (h : AreaSetup K hm R) {Sg : ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : b - a ≤ 1 / 2) (hσS : arcFn K b - arcFn K a ≤ Sg)
    (hsmall : 16 * (b - a) * (R + Sg + 1) ≤ hm) :
    secR K a b = curveG K a b := by
  have hKc := h.isCompact
  have hKne := h.nonempty
  have hm0 := h.hm_pos
  have hR0 := h.R_nonneg
  have hσ0 : 0 ≤ arcFn K b - arcFn K a := by linarith [arcFn_mono hKc hKne hab]
  have hSg0 : 0 ≤ Sg := le_trans hσ0 hσS
  obtain ⟨M, hM1, hMR, hMS⟩ : ∃ M : ℝ, 1 ≤ M ∧ R ≤ M ∧ Sg ≤ M :=
    ⟨max 1 (max R Sg), le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have hM0 : (0:ℝ) < M := by linarith
  obtain ⟨C, hC⟩ : ∃ C : ℝ, 71 * M ^ 3 ≤ hm ^ 2 * (2 * C) :=
    ⟨71 * M ^ 3 / (2 * hm ^ 2), by
      have he : hm ^ 2 * (2 * (71 * M ^ 3 / (2 * hm ^ 2))) = 71 * M ^ 3 := by
        field_simp
      exact le_of_eq he.symm⟩
  have hC0 : 0 ≤ C := by nlinarith only [hC, pow_pos hM0 3, pow_pos hm0 2]
  obtain ⟨D, hD⟩ : ∃ D : ℝ → ℝ → ℝ, D = fun x y => secR K x y - curveG K x y := ⟨_, rfl⟩
  -- additivity
  have hDadd : ∀ x y z : ℝ, a ≤ x → x ≤ y → y ≤ z → z ≤ b → D x z = D x y + D y z := by
    intro x y z hax hxy hyz hzb
    have hS : arcFn K z - arcFn K x ≤ Sg := by
      have h1 := arcFn_mono hKc hKne hax
      have h2 := arcFn_mono hKc hKne hzb
      linarith
    have hsm : 16 * (z - x) * (R + Sg + 1) ≤ hm := by
      have h1 : (0:ℝ) ≤ R + Sg + 1 := by linarith
      have h2 : z - x ≤ b - a := by linarith
      nlinarith only [mul_le_mul_of_nonneg_right h2 h1, hsmall]
    simp only [hD]
    rw [secR_add' h hxy hyz (by linarith) hS hsm, curveG_add hKc hKne hxy hyz]
    ring
  -- the local estimate on every subinterval
  have hlocal : ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ b →
      |D x y| ≤ C * (y - x) * (arcFn K y - arcFn K x) := by
    intro x y hax hxy hyb
    simp only [hD]
    refine abs_secR_sub_curveG_le h hM1 hMR hMS hC hxy (by linarith) ?_ ?_
    · have h1 := arcFn_mono hKc hKne hax
      have h2 := arcFn_mono hKc hKne hyb
      linarith
    · have h1 : (0:ℝ) ≤ R + Sg + 1 := by linarith
      have h2 : y - x ≤ b - a := by linarith
      nlinarith only [mul_le_mul_of_nonneg_right h2 h1, hsmall]
  -- chaining
  have hchain : ∀ δ : ℝ, 0 < δ → ∀ n : ℕ, ∀ x y : ℝ, a ≤ x → x ≤ y → y ≤ b →
      y ≤ x + n * δ → |D x y| ≤ C * δ * (arcFn K y - arcFn K x) := by
    intro δ hδ0 n
    induction n with
    | zero =>
      intro x y hax hxy hyb hy
      simp only [Nat.cast_zero, zero_mul, add_zero] at hy
      have hxy' : x = y := le_antisymm hxy hy
      subst hxy'
      have h1 : secR K x x = 0 :=
        secR_eq_zero_of_arcFn_eq h le_rfl (by rw [sub_self]; linarith [pi_gt_three]) rfl
      have h2 : curveG K x x = 0 := curveG_eq_zero_of_arcFn_eq hKc hKne le_rfl rfl
      simp [hD, h1, h2]
    | succ n ih =>
      intro x y hax hxy hyb hy
      have hmono : (0:ℝ) ≤ arcFn K y - arcFn K x := by linarith [arcFn_mono hKc hKne hxy]
      rcases le_or_gt y (x + δ) with h1 | h1
      · have hst := hlocal x y hax hxy hyb
        have hkey : 0 ≤ (C * (δ - (y - x))) * (arcFn K y - arcFn K x) :=
          mul_nonneg (mul_nonneg hC0 (by linarith)) hmono
        nlinarith only [hkey, hst]
      · have h2 : x + δ ≤ y := h1.le
        have hax' : a ≤ x + δ := by linarith
        have hstep : |D x (x + δ)| ≤ C * δ * (arcFn K (x + δ) - arcFn K x) := by
          have hh := hlocal x (x + δ) hax (by linarith) (by linarith)
          rw [show x + δ - x = δ by ring] at hh
          exact hh
        have hrest : |D (x + δ) y| ≤ C * δ * (arcFn K y - arcFn K (x + δ)) := by
          refine ih (x + δ) y hax' h2 hyb ?_
          push_cast at hy ⊢
          linarith
        rw [hDadd x (x + δ) y hax (by linarith) h2 hyb]
        refine le_trans (abs_add_le _ _) ?_
        linarith
  have hall : ∀ δ : ℝ, 0 < δ → |D a b| ≤ C * δ * (arcFn K b - arcFn K a) := by
    intro δ hδ0
    obtain ⟨n, hn⟩ := exists_nat_ge ((b - a) / δ)
    refine hchain δ hδ0 n a b le_rfl hab le_rfl ?_
    have := (div_le_iff₀ hδ0).1 hn
    linarith
  have hzero : D a b = 0 := by
    by_contra hcon
    have hpos : 0 < |D a b| := abs_pos.2 hcon
    obtain ⟨c, hcge, hcpos⟩ : ∃ c : ℝ, C * (arcFn K b - arcFn K a) ≤ c ∧ 0 < c :=
      ⟨C * (arcFn K b - arcFn K a) + 1, by linarith,
        by nlinarith only [mul_nonneg hC0 hσ0]⟩
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min 1 (|D a b| / (2 * c)) := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by
      rw [hδdef]; exact lt_min one_pos (div_pos hpos (by linarith))
    have hδ2 : δ ≤ |D a b| / (2 * c) := by rw [hδdef]; exact min_le_right _ _
    have hh := hall δ hδ0
    have hc2 : c * δ ≤ |D a b| / 2 := by
      have h6 := (le_div_iff₀ (by linarith : (0:ℝ) < 2 * c)).1 hδ2
      linarith
    have h5 : (C * (arcFn K b - arcFn K a)) * δ ≤ c * δ :=
      mul_le_mul_of_nonneg_right hcge hδ0.le
    linarith
  simp only [hD] at hzero
  linarith [hzero]

end Sofa
