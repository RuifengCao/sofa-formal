/-
# Sofa/QMax.lean — Baek Theorem 8.5.7 (abstract form): `D𝒬 ≤ 0` at a triple with Gerver's structure

Baek proves `D𝒬(P_G; P') ≤ 0` for the triple `P_G = (K, B_K, D_K)` of Gerver's cap by splitting
the directional derivative of Thm 8.5.6 over the intervals `J₁, …, J₁₀` of Def 8.4.7, using

* **Thm 8.4.3 (3)**: `h_K(t) + h_B(π + t) = 1` on `[π/2 − θ, π/2]` and
  `h_K(π/2 + t) + h_D(3π/2 + t) = 1` on `[0, θ]`;
* **Thm 8.4.3 (2)**: the tails start at the core ends, so `σ_B` vanishes on `(π + φ, 3π/2 − θ)` and
  `σ_D` on `(3π/2 + θ, 2π − φ)`;
* **Thm 8.4.5**: the ten measure identities `σ_K = 0 | ι_K | σ̆_B + ι_K | σ̆_B` on `J₁ … J₅`, and
  `σ̆_D | σ̆_D + ι_K | ι_K | 0` on `J₆ … J₁₀`.

Here these facts are the fields of `GerverData φ θ K B D`; the identities of Thm 8.4.5 are stated
in the equivalent grouped form `σ_K|_{[0,π/2)} = ι_K|_{[φ, π/2−φ)} + σ̆_B|_{[π/2−θ, π/2)}` and
`σ_K|_{(π/2, π]} = ι_K|_{(π/2+φ, π−φ]} + σ̆_D|_{(π/2, π/2+θ]}`.  From them we prove
(`GerverData.dirQ_nonpos`) that the directional derivative `dirQ` is `≤ 0` towards every triple
satisfying the inequalities of `𝓛`, and hence (`GerverData.Qfun_le`, Cor 8.5.8) that `𝒬` attains
its maximum on `𝓛` at such a triple.

The only property of caps used beyond `GerverData` is that a cap has no boundary strictly between
its two lower corners and the floor: `σ_K((π, 3π/2)) = σ_K((3π/2, 2π)) = 0`
(`IsCap.sigmaK_Ioo_pi`, `IsCap.sigmaK_Ioo_three_pi_div_two`), so that
`⟨f, σ_K⟩_{S¹} = ⟨f, σ_K⟩_{[0, π]}` when `f(3π/2) = 0` (Baek's Thm 8.5.1 is stated over `[0, π]`).

STATUS: [PROOF-C-local] round 33 (2026-09-23, Opus 5.5).
-/
import Sofa.DirDerivQ

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace Interval

namespace Sofa

/-! ## A Stieltjes measure vanishes where its function is constant -/

lemma StieltjesFunction.measure_Ioo_eq_zero_of_const (F : StieltjesFunction ℝ) {a b c : ℝ}
    (hab : a < b) (h : ∀ x ∈ Ioo a b, F x = c) : F.measure (Ioo a b) = 0 := by
  rw [StieltjesFunction.measure_Ioo]
  have hL : Function.leftLim F b = c := by
    refine leftLim_eq_of_tendsto (f := ⇑F) ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hab] with x hx
    exact (h x hx).symm
  have hR : F a = c := by
    have h1 : Tendsto F (𝓝[>] a) (𝓝 (F a)) := (F.right_continuous a).mono Ioi_subset_Ici_self
    have h2 : Tendsto F (𝓝[>] a) (𝓝 c) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hab] with x hx
      exact (h x hx).symm
    exact tendsto_nhds_unique h1 h2
  rw [hL, hR, sub_self, ENNReal.ofReal_zero]

/-! ## The lower boundary of a cap -/

section Cap

variable {K : Set ℝ²} (hK : IsCap K (π / 2))
include hK

/-- On `(π, 3π/2)` the right vertex of a cap is its lower-left corner: `e⁺_K(t) = h_K(π) sin t`. -/
lemma IsCap.edgeMax_of_mem_Ioo_pi {t : ℝ} (ht : t ∈ Ioo π (3 * π / 2)) :
    edgeMax K t = supportFn K π * sin t := by
  have hev : supportFn K =ᶠ[𝓝 t] fun s => -supportFn K π * cos s :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs =>
      hK.supportFn_of_mem_Icc_pi (Ioo_subset_Icc_self hs)
  have hd : HasDerivAt (supportFn K) (supportFn K π * sin t) t :=
    (((hasDerivAt_cos t).const_mul (-supportFn K π)).congr_of_eventuallyEq hev).congr_deriv
      (by ring)
  exact (uniqueDiffWithinAt_Ioi t).eq_deriv _
    (hasDerivWithinAt_supportFn_Ioi hK.isCompact hK.nonempty t) hd.hasDerivWithinAt

/-- On `(3π/2, 2π)` the right vertex of a cap is its lower-right corner: `e⁺_K(t) = −h_K(0) sin t`. -/
lemma IsCap.edgeMax_of_mem_Ioo_three_pi_div_two {t : ℝ} (ht : t ∈ Ioo (3 * π / 2) (2 * π)) :
    edgeMax K t = -(supportFn K 0 * sin t) := by
  have hev : supportFn K =ᶠ[𝓝 t] fun s => supportFn K 0 * cos s :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht.1 ht.2) fun s hs =>
      hK.supportFn_of_mem_Icc_three_pi_div_two (Ioo_subset_Icc_self hs)
  have hd : HasDerivAt (supportFn K) (-(supportFn K 0 * sin t)) t :=
    (((hasDerivAt_cos t).const_mul (supportFn K 0)).congr_of_eventuallyEq hev).congr_deriv
      (by ring)
  exact (uniqueDiffWithinAt_Ioi t).eq_deriv _
    (hasDerivWithinAt_supportFn_Ioi hK.isCompact hK.nonempty t) hd.hasDerivWithinAt

/-- `σ_K((π, 3π/2)) = 0`. -/
theorem IsCap.sigmaK_Ioo_pi : sigmaK K (Ioo π (3 * π / 2)) = 0 := by
  have hKc := hK.isCompact
  have hne := hK.nonempty
  have hpi := pi_pos
  rw [sigmaK_eq hKc hne]
  refine StieltjesFunction.measure_Ioo_eq_zero_of_const _ (by linarith)
    (c := ∫ s in (0:ℝ)..π, supportFn K s) fun t ht => ?_
  simp only [arcSF_apply]
  have harc : arcFn K t = edgeMax K t + ∫ s in (0:ℝ)..t, supportFn K s := by
    have := edgeMax_eq_arcFn_sub K t; linarith
  have hint : ∫ s in π..t, supportFn K s = -(supportFn K π * sin t) := by
    rw [intervalIntegral.integral_congr (g := fun s => -supportFn K π * cos s) ?_,
      intervalIntegral.integral_const_mul, integral_cos, sin_pi]
    · ring
    intro s hs
    rw [uIcc_of_le ht.1.le] at hs
    exact hK.supportFn_of_mem_Icc_pi ⟨hs.1, hs.2.trans ht.2.le⟩
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (integrable_supportFn hKc hne 0 π) (integrable_supportFn hKc hne π t)
  rw [harc, hK.edgeMax_of_mem_Ioo_pi ht, ← hsplit, hint]
  ring

/-- `σ_K((3π/2, 2π)) = 0`. -/
theorem IsCap.sigmaK_Ioo_three_pi_div_two : sigmaK K (Ioo (3 * π / 2) (2 * π)) = 0 := by
  have hKc := hK.isCompact
  have hne := hK.nonempty
  have hpi := pi_pos
  rw [sigmaK_eq hKc hne]
  refine StieltjesFunction.measure_Ioo_eq_zero_of_const _ (by linarith)
    (c := (∫ s in (0:ℝ)..(3 * π / 2), supportFn K s) - supportFn K 0 * sin (3 * π / 2))
    fun t ht => ?_
  simp only [arcSF_apply]
  have harc : arcFn K t = edgeMax K t + ∫ s in (0:ℝ)..t, supportFn K s := by
    have := edgeMax_eq_arcFn_sub K t; linarith
  have hint : ∫ s in (3 * π / 2)..t, supportFn K s
      = supportFn K 0 * (sin t - sin (3 * π / 2)) := by
    rw [intervalIntegral.integral_congr (g := fun s => supportFn K 0 * cos s) ?_,
      intervalIntegral.integral_const_mul, integral_cos]
    intro s hs
    rw [uIcc_of_le ht.1.le] at hs
    exact hK.supportFn_of_mem_Icc_three_pi_div_two ⟨hs.1, hs.2.trans ht.2.le⟩
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (integrable_supportFn hKc hne 0 (3 * π / 2)) (integrable_supportFn hKc hne (3 * π / 2) t)
  rw [harc, hK.edgeMax_of_mem_Ioo_three_pi_div_two ht, ← hsplit, hint]
  ring

end Cap

lemma edgeMin_add_two_pi (K : Set ℝ²) (t : ℝ) : edgeMin K (t + 2 * π) = edgeMin K t := by
  rw [edgeMin, edgeMin, edge_add_two_pi,
    show t + 2 * π + π / 2 + π = t + π / 2 + π + 2 * π by ring, supportFn_add_two_pi]

lemma edgeLength_add_two_pi (K : Set ℝ²) (t : ℝ) :
    edgeLength K (t + 2 * π) = edgeLength K t := by
  rw [edgeLength, edgeLength, edgeMax_add_two_pi, edgeMin_add_two_pi]

/-- `∫_{(a,b]} f dμ = μ({b}) f(b)` when `μ((a,b)) = 0`. -/
lemma setIntegral_Ioc_of_null {μ : Measure ℝ} {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hint : IntegrableOn f (Ioc a b) μ) (h0 : μ (Ioo a b) = 0) :
    ∫ t in Ioc a b, f t ∂μ = μ.real {b} * f b := by
  rw [← Ioo_union_right hab, setIntegral_union
    (Set.disjoint_singleton_right.2 fun h => lt_irrefl _ h.2) (measurableSet_singleton b)
    (hint.mono_set Ioo_subset_Ioc_self)
    (hint.mono_set (singleton_subset_iff.2 ⟨hab, le_rfl⟩)),
    setIntegral_measure_zero _ h0, integral_singleton, smul_eq_mul, zero_add]

/-- Splitting a set integral over adjacent half-open intervals. -/
lemma setIntegral_Ioc_split {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Continuous f) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∫ t in Ioc a c, f t ∂μ = (∫ t in Ioc a b, f t ∂μ) + ∫ t in Ioc b c, f t ∂μ := by
  rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hbc,
    ← intervalIntegral.integral_of_le (hab.trans hbc),
    intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable a b)
      (hf.intervalIntegrable b c)]

/-- **For a cap**, `⟨f, σ_K⟩_{(0, 2π]} = ⟨f, σ_K⟩_{[0, π]}` when `f(3π/2) = 0` and `f(2π) = f(0)`. -/
theorem IsCap.setIntegral_Ioc_zero_two_pi {K : Set ℝ²} (hK : IsCap K (π / 2)) {f : ℝ → ℝ}
    (hf : Continuous f) (h32 : f (3 * π / 2) = 0) (h2 : f (2 * π) = f 0) :
    ∫ t in Ioc 0 (2 * π), f t ∂(sigmaK K) = ∫ t in Icc 0 π, f t ∂(sigmaK K) := by
  have hKc := hK.isCompact
  have hne := hK.nonempty
  have hpi := pi_pos
  have hint : ∀ a b : ℝ, IntegrableOn f (Ioc a b) (sigmaK K) := fun a b =>
    (hf.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  rw [setIntegral_Ioc_split hf (b := π) (by linarith) (by linarith),
    setIntegral_Ioc_split hf (a := π) (b := 3 * π / 2) (by linarith) (by linarith),
    setIntegral_Ioc_of_null (by linarith) (hint _ _) hK.sigmaK_Ioo_pi,
    setIntegral_Ioc_of_null (by linarith) (hint _ _) hK.sigmaK_Ioo_three_pi_div_two, h32, h2,
    ← Ioc_insert_left (show (0:ℝ) ≤ π by linarith), insert_eq,
    setIntegral_union (Set.disjoint_singleton_left.2 fun h => lt_irrefl _ h.1)
      measurableSet_Ioc (hf.continuousOn.integrableOn_compact isCompact_singleton) (hint _ _),
    integral_singleton, smul_eq_mul]
  have hsing : (sigmaK K).real {2 * π} = (sigmaK K).real {0} := by
    rw [measureReal_def, measureReal_def, sigmaK_singleton hKc hne, sigmaK_singleton hKc hne,
      show (2 * π : ℝ) = 0 + 2 * π by ring, edgeLength_add_two_pi]
  rw [hsing]
  ring

/-! ## The measures `σ̆_C` (Def 8.4.5) and `ι_K` (Def 8.4.6) -/

/-- **Baek Def 8.4.5**: `σ̆_C(X) = σ_C(X + π)`. -/
def sigmaBreve (C : Set ℝ²) : Measure ℝ := (sigmaK C).map (fun s => s - π)

/-- The density `i_K` of `ι_K` (Baek Def 8.4.6): `iotaV` on `(−∞, π/2]`, `iotaU(· − π/2)` beyond. -/
def iotaDens (K : Set ℝ²) (t : ℝ) : ℝ := if t ≤ π / 2 then iotaV K t else iotaU K (t - π / 2)

/-- **Baek Def 8.4.6**: the measure `ι_K(dt) = i_K(t) dt` (only its restrictions to subintervals of
`[φ, π − φ]`, where `i_K ≥ 0`, are used). -/
def iotaK (K : Set ℝ²) : Measure ℝ := volume.withDensity fun t => ENNReal.ofReal (iotaDens K t)

lemma measurable_iotaV {K : Set ℝ²} (hK : IsCompact K) (hne : K.Nonempty) :
    Measurable (iotaV K) := by
  show Measurable fun t => supportFn K t - 1 + edgeMax K (t + π / 2)
  exact ((continuous_supportFn hK hne).measurable.sub_const 1).add
    ((measurable_edgeMax hK hne).comp (measurable_add_const _))

lemma measurable_iotaU {K : Set ℝ²} (hK : IsCompact K) (hne : K.Nonempty) :
    Measurable (iotaU K) := by
  show Measurable fun t => supportFn K (t + π / 2) - 1 - edgeMax K t
  exact (((continuous_supportFn hK hne).comp (continuous_add_const _)).measurable.sub_const 1).sub
    (measurable_edgeMax hK hne)

lemma measurable_iotaDens {K : Set ℝ²} (hK : IsCompact K) (hne : K.Nonempty) :
    Measurable (iotaDens K) :=
  Measurable.ite measurableSet_Iic (measurable_iotaV hK hne)
    ((measurable_iotaU hK hne).comp (measurable_sub_const _))

/-- `⟨f, ι_K⟩_{[φ, π/2−φ)} = ∫_φ^{π/2−φ} f · i_K`. -/
lemma setIntegral_iotaK_left {K : Set ℝ²} (hK : IsCompact K) (hne : K.Nonempty) {φ : ℝ}
    (hφ0 : 0 ≤ φ) (hφ : φ ≤ π / 2 - φ) (hnn : ∀ t ∈ Icc φ (π / 2 - φ), 0 ≤ iotaV K t) (f : ℝ → ℝ) :
    ∫ t in Ico φ (π / 2 - φ), f t ∂(iotaK K) = ∫ t in φ..(π / 2 - φ), f t * iotaV K t := by
  have hpi := pi_pos
  rw [iotaK, setIntegral_withDensity_eq_setIntegral_toReal_smul
      (measurable_iotaDens hK hne).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f measurableSet_Ico,
    intervalIntegral.integral_of_le hφ, integral_Ico_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht' : t ≤ π / 2 := by linarith [ht.2]
  simp only [iotaDens, if_pos ht', smul_eq_mul]
  rw [ENNReal.toReal_ofReal (hnn t ⟨ht.1.le, ht.2.le⟩), mul_comm]

/-- `⟨f, ι_K⟩_{(π/2+φ, π−φ]} = ∫_φ^{π/2−φ} f(· + π/2) · i_K(· + π/2)`. -/
lemma setIntegral_iotaK_right {K : Set ℝ²} (hK : IsCompact K) (hne : K.Nonempty) {φ : ℝ}
    (hφ0 : 0 ≤ φ) (hφ : φ ≤ π / 2 - φ) (hnn : ∀ t ∈ Icc φ (π / 2 - φ), 0 ≤ iotaU K t) (f : ℝ → ℝ) :
    ∫ t in Ioc (π / 2 + φ) (π - φ), f t ∂(iotaK K)
      = ∫ t in φ..(π / 2 - φ), f (t + π / 2) * iotaU K t := by
  have hpi := pi_pos
  rw [iotaK, setIntegral_withDensity_eq_setIntegral_toReal_smul
      (measurable_iotaDens hK hne).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f measurableSet_Ioc]
  have e1 := intervalIntegral.integral_comp_add_right
    (f := fun s => f s * iotaU K (s - π / 2)) (a := φ) (b := π / 2 - φ) (π / 2)
  simp only [add_sub_cancel_right] at e1
  rw [e1, show φ + π / 2 = π / 2 + φ by ring, show π / 2 - φ + π / 2 = π - φ by ring,
    intervalIntegral.integral_of_le (by linarith)]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  have ht' : ¬ t ≤ π / 2 := by linarith [ht.1]
  simp only [iotaDens, if_neg ht', smul_eq_mul]
  rw [ENNReal.toReal_ofReal (hnn (t - π / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩), mul_comm]

/-- `⟨f, σ̆_C⟩_S = ⟨f(· − π), σ_C⟩_{S + π}`. -/
lemma setIntegral_sigmaBreve (C : Set ℝ²) {f : ℝ → ℝ} (hf : Continuous f) {S : Set ℝ}
    (hS : MeasurableSet S) :
    ∫ t in S, f t ∂(sigmaBreve C) = ∫ s in (fun s => s - π) ⁻¹' S, f (s - π) ∂(sigmaK C) :=
  setIntegral_map hS hf.aestronglyMeasurable (measurable_sub_const π).aemeasurable

/-! ## Gerver's structure and Theorem 8.5.7 -/

variable {φ θ : ℝ} {K B D K' B' D' : Set ℝ²}

/-- **The properties of Gerver's triple** `(K, B, D) = (C(G), B_{C(G)}, D_{C(G)})` that Baek's
proof of Theorem 8.5.7 uses, for Gerver's angles `0 < φ < θ < π/4` (Def 8.1.2, Def 8.4.1):
Thm 8.1.8 (the equalities of `𝓛`), Thm 8.4.3 (2)–(3), Thm 8.4.5, and `f_K, g_K ≥ 1` on the core
(Def 6.1.2 (3), via Thm 6.1.2).  Baek derives them from Thm 8.4.1–8.4.2, which he does not prove
(Rem 8.4.1). -/
structure GerverData (φ θ : ℝ) (K B D : Set ℝ²) : Prop where
  phi_pos : 0 < φ
  phi_lt_theta : φ < θ
  theta_lt : θ < π / 4
  cap : IsCap K (π / 2)
  interior_nonempty : (interior K).Nonempty
  B_compact : IsCompact B
  B_nonempty : B.Nonempty
  D_compact : IsCompact D
  D_nonempty : D.Nonempty
  /-- the equalities of `𝓛` (Def 8.1.3 (3), (5); Thm 8.1.8) -/
  leq : LEq φ K B D
  /-- Thm 8.4.3 (2): `X_B = x^R_K` -/
  X_B : vtxP B (π + φ) = innerCorner K φ
  /-- Thm 8.4.3 (2): `Y_D = x^L_K` -/
  Y_D : vtxM D (2 * π - φ) = innerCorner K (π / 2 - φ)
  /-- Thm 8.4.3 (2): `b_B = B` is traced over `[t₃, t₅] = [π/2 − θ, π/2]`, so `σ_B` vanishes on
  `(π + φ, π + t₃)` -/
  B_null : sigmaK B (Ioo (π + φ) (3 * π / 2 - θ)) = 0
  /-- Thm 8.4.3 (2): `d_D = D` is traced over `[t₀, t₂] = [0, θ]` -/
  D_null : sigmaK D (Ioo (3 * π / 2 + θ) (2 * π - φ)) = 0
  /-- Thm 8.4.3 (3) -/
  B_eq : ∀ t ∈ Icc (π / 2 - θ) (π / 2), supportFn K t + supportFn B (π + t) = 1
  /-- Thm 8.4.3 (3) -/
  D_eq : ∀ t ∈ Icc 0 θ, supportFn K (π / 2 + t) + supportFn D (3 * π / 2 + t) = 1
  /-- Thm 8.4.5 (1)–(4): `σ_K = 0 | ι_K | σ̆_B + ι_K | σ̆_B` on `J₁ | J₂ ∪ J₃ | J₄ | J₅` -/
  sigma_left : (sigmaK K).restrict (Ico 0 (π / 2))
    = (iotaK K).restrict (Ico φ (π / 2 - φ)) + (sigmaBreve B).restrict (Ico (π / 2 - θ) (π / 2))
  /-- Thm 8.4.5 (5)–(8): `σ_K = σ̆_D | σ̆_D + ι_K | ι_K | 0` on `J₆ | J₇ | J₈ ∪ J₉ | J₁₀` -/
  sigma_right : (sigmaK K).restrict (Ioc (π / 2) π)
    = (iotaK K).restrict (Ioc (π / 2 + φ) (π - φ))
      + (sigmaBreve D).restrict (Ioc (π / 2) (π / 2 + θ))
  /-- `i_K = g_K − 1 ≥ 0` on the core `I = [φ, π/2 − φ]` -/
  iotaV_nonneg : ∀ t ∈ Icc φ (π / 2 - φ), 0 ≤ iotaV K t
  /-- `i_K(· + π/2) = f_K − 1 ≥ 0` on `I` -/
  iotaU_nonneg : ∀ t ∈ Icc φ (π / 2 - φ), 0 ≤ iotaU K t

/-- **Baek Theorem 8.5.7** (abstract form): at a triple with Gerver's structure, the directional
derivative of `𝒬` towards any triple satisfying the inequalities of `𝓛` is nonpositive. -/
theorem GerverData.dirQ_nonpos (hG : GerverData φ θ K B D) (hK' : IsCap K' (π / 2))
    (hB' : IsCompact B') (hB'ne : B'.Nonempty) (hD' : IsCompact D') (hD'ne : D'.Nonempty)
    (hBle : ∀ t ∈ Icc φ (π / 2), supportFn K' t + supportFn B' (π + t) ≤ 1)
    (hDle : ∀ t ∈ Icc 0 (π / 2 - φ),
      supportFn K' (π / 2 + t) + supportFn D' (3 * π / 2 + t) ≤ 1) :
    dirQ φ K B D K' B' D' ≤ 0 := by
  have hpi := pi_pos
  have hφ0 := hG.phi_pos
  have hφθ := hG.phi_lt_theta
  have hθ := hG.theta_lt
  have hK := hG.cap
  have hKc := hK.isCompact
  have hKne := hK.nonempty
  have hK'c := hK'.isCompact
  have hK'ne := hK'.nonempty
  have hB := hG.B_compact
  have hBne := hG.B_nonempty
  have hD := hG.D_compact
  have hDne := hG.D_nonempty
  have cK := continuous_supportFn hKc hKne
  have cK' := continuous_supportFn hK'c hK'ne
  have cΔ : Continuous fun t => supportFn K' t - supportFn K t := cK'.sub cK
  have cΔB : Continuous fun t => supportFn B' t - supportFn B t :=
    (continuous_supportFn hB' hB'ne).sub (continuous_supportFn hB hBne)
  have cΔD : Continuous fun t => supportFn D' t - supportFn D t :=
    (continuous_supportFn hD' hD'ne).sub (continuous_supportFn hD hDne)
  have cΔπ : Continuous fun s => supportFn K' (s - π) - supportFn K (s - π) :=
    cΔ.comp (continuous_sub_right π)
  -- Step 1: `⟨Δ, σ_K⟩_{S¹} = ⟨Δ, σ_K⟩_{[0, π]}`
  have s1 := hK.setIntegral_Ioc_zero_two_pi cΔ
    (by show supportFn K' (3 * π / 2) - supportFn K (3 * π / 2) = 0
        rw [hK.supportFn_three_pi_div_two, hK'.supportFn_three_pi_div_two, sub_zero])
    (by show supportFn K' (2 * π) - supportFn K (2 * π) = supportFn K' 0 - supportFn K 0
        rw [show (2 : ℝ) * π = 0 + 2 * π by ring, supportFn_add_two_pi, supportFn_add_two_pi])
  -- Step 2: split `[0, π] = [0, π/2) ∪ {π/2} ∪ (π/2, π]`; `Δ(π/2) = 0`
  have s2 : ∫ t in Icc 0 π, (supportFn K' t - supportFn K t) ∂(sigmaK K)
      = (∫ t in Ico 0 (π / 2), (supportFn K' t - supportFn K t) ∂(sigmaK K))
        + ∫ t in Ioc (π / 2) π, (supportFn K' t - supportFn K t) ∂(sigmaK K) := by
    have hi : ∀ S : Set ℝ, S ⊆ Icc 0 π →
        IntegrableOn (fun t => supportFn K' t - supportFn K t) S (sigmaK K) := fun S hS =>
      (cΔ.continuousOn.integrableOn_compact isCompact_Icc).mono_set hS
    rw [← Ico_union_Icc_eq_Icc (show (0:ℝ) ≤ π / 2 by linarith) (show π / 2 ≤ π by linarith),
      setIntegral_union (Set.disjoint_left.2 fun x hx1 hx2 => absurd hx2.1 (not_le.2 hx1.2))
        measurableSet_Icc (hi _ fun x hx => ⟨hx.1, by linarith [hx.2]⟩)
        (hi _ fun x hx => ⟨by linarith [hx.1], hx.2⟩),
      ← Ioc_insert_left (show π / 2 ≤ π by linarith), insert_eq,
      setIntegral_union (Set.disjoint_singleton_left.2 fun h => lt_irrefl _ h.1)
        measurableSet_Ioc (hi _ (singleton_subset_iff.2 ⟨by linarith, by linarith⟩))
        (hi _ fun x hx => ⟨by linarith [hx.1], hx.2⟩),
      integral_singleton, hK.supportFn_pi_div_two, hK'.supportFn_pi_div_two, sub_self,
      smul_zero, zero_add]
  -- Step 3: the left half, by Thm 8.4.5 (1)–(4)
  have s3 : ∫ t in Ico 0 (π / 2), (supportFn K' t - supportFn K t) ∂(sigmaK K)
      = (∫ t in φ..(π / 2 - φ), (supportFn K' t - supportFn K t) * iotaV K t)
        + ∫ s in Ico (3 * π / 2 - θ) (3 * π / 2),
            (supportFn K' (s - π) - supportFn K (s - π)) ∂(sigmaK B) := by
    have hint : Integrable (fun t => supportFn K' t - supportFn K t)
        ((sigmaK K).restrict (Ico 0 (π / 2))) :=
      (cΔ.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self
    rw [hG.sigma_left] at hint
    obtain ⟨h1, h2⟩ := integrable_add_measure.1 hint
    rw [hG.sigma_left, integral_add_measure h1 h2,
      setIntegral_iotaK_left hKc hKne hφ0.le (by linarith) hG.iotaV_nonneg,
      setIntegral_sigmaBreve B cΔ measurableSet_Ico, Set.preimage_sub_const_Ico,
      show π / 2 - θ + π = 3 * π / 2 - θ by ring, show π / 2 + π = 3 * π / 2 by ring]
  -- Step 4: the right half, by Thm 8.4.5 (5)–(8)
  have s4 : ∫ t in Ioc (π / 2) π, (supportFn K' t - supportFn K t) ∂(sigmaK K)
      = (∫ t in φ..(π / 2 - φ),
            (supportFn K' (t + π / 2) - supportFn K (t + π / 2)) * iotaU K t)
        + ∫ s in Ioc (3 * π / 2) (3 * π / 2 + θ),
            (supportFn K' (s - π) - supportFn K (s - π)) ∂(sigmaK D) := by
    have hint : Integrable (fun t => supportFn K' t - supportFn K t)
        ((sigmaK K).restrict (Ioc (π / 2) π)) :=
      (cΔ.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    rw [hG.sigma_right] at hint
    obtain ⟨h1, h2⟩ := integrable_add_measure.1 hint
    rw [hG.sigma_right, integral_add_measure h1 h2,
      setIntegral_iotaK_right hKc hKne hφ0.le (by linarith) hG.iotaU_nonneg,
      setIntegral_sigmaBreve D cΔ measurableSet_Ioc, Set.preimage_sub_const_Ioc,
      show π / 2 + π = 3 * π / 2 by ring, show π / 2 + θ + π = 3 * π / 2 + θ by ring]
  -- Step 5: the tail `b_B` starts at `π + t₃`
  have s5 : ∫ t in Ioo (π + φ) (3 * π / 2), (supportFn B' t - supportFn B t) ∂(sigmaK B)
      = ∫ s in Ico (3 * π / 2 - θ) (3 * π / 2), (supportFn B' s - supportFn B s) ∂(sigmaK B) := by
    have hi : ∀ S : Set ℝ, S ⊆ Icc (π + φ) (3 * π / 2) →
        IntegrableOn (fun t => supportFn B' t - supportFn B t) S (sigmaK B) := fun S hS =>
      (cΔB.continuousOn.integrableOn_compact isCompact_Icc).mono_set hS
    rw [← Ioo_union_Ico_eq_Ioo (show π + φ < 3 * π / 2 - θ by linarith)
        (show 3 * π / 2 - θ ≤ 3 * π / 2 by linarith),
      setIntegral_union (Set.disjoint_left.2 fun x hx1 hx2 => absurd hx2.1 (not_le.2 hx1.2))
        measurableSet_Ico (hi _ fun x hx => ⟨hx.1.le, by linarith [hx.2]⟩)
        (hi _ fun x hx => ⟨by linarith [hx.1], hx.2.le⟩),
      setIntegral_measure_zero _ hG.B_null, zero_add]
  -- Step 6: the tail `d_D` ends at `3π/2 + t₂`
  have s6 : ∫ t in Ioo (3 * π / 2) (2 * π - φ), (supportFn D' t - supportFn D t) ∂(sigmaK D)
      = ∫ s in Ioc (3 * π / 2) (3 * π / 2 + θ), (supportFn D' s - supportFn D s) ∂(sigmaK D) := by
    have hi : ∀ S : Set ℝ, S ⊆ Icc (3 * π / 2) (2 * π - φ) →
        IntegrableOn (fun t => supportFn D' t - supportFn D t) S (sigmaK D) := fun S hS =>
      (cΔD.continuousOn.integrableOn_compact isCompact_Icc).mono_set hS
    rw [← Ioc_union_Ioo_eq_Ioo (show 3 * π / 2 ≤ 3 * π / 2 + θ by linarith)
        (show 3 * π / 2 + θ < 2 * π - φ by linarith),
      setIntegral_union (Set.disjoint_left.2 fun x hx1 hx2 => absurd hx1.2 (not_le.2 hx2.1))
        measurableSet_Ioo (hi _ fun x hx => ⟨hx.1.le, by linarith [hx.2]⟩)
        (hi _ fun x hx => ⟨hx.1.le.trans' (by linarith), hx.2.le⟩),
      setIntegral_measure_zero _ hG.D_null, add_zero]
  -- Step 7: the `ι`-term of `dirQ` splits
  have iV : IntervalIntegrable (iotaV K) volume φ (π / 2 - φ) :=
    ((cK.sub continuous_const).intervalIntegrable _ _).add
      (intervalIntegrable_edgeMax_add hKc hKne _ _ _)
  have iU : IntervalIntegrable (iotaU K) volume φ (π / 2 - φ) :=
    (((cK.comp (continuous_add_const _)).sub continuous_const).intervalIntegrable _ _).sub
      (intervalIntegrable_edgeMax hKc hKne _ _)
  have s7 : ∫ t in φ..(π / 2 - φ), ((supportFn K' t - supportFn K t) * iotaV K t
        + (supportFn K' (t + π / 2) - supportFn K (t + π / 2)) * iotaU K t)
      = (∫ t in φ..(π / 2 - φ), (supportFn K' t - supportFn K t) * iotaV K t)
        + ∫ t in φ..(π / 2 - φ),
            (supportFn K' (t + π / 2) - supportFn K (t + π / 2)) * iotaU K t :=
    intervalIntegral.integral_add (iV.continuousOn_mul cΔ.continuousOn)
      (iU.continuousOn_mul (cΔ.comp (continuous_add_const _)).continuousOn)
  -- Step 8: the two remaining sums are `≤ 0` (Thm 8.4.3 (3) and Lemma 8.1.7 (1), (3))
  have n1 : (∫ s in Ico (3 * π / 2 - θ) (3 * π / 2),
        (supportFn K' (s - π) - supportFn K (s - π)) ∂(sigmaK B))
      + (∫ s in Ico (3 * π / 2 - θ) (3 * π / 2), (supportFn B' s - supportFn B s) ∂(sigmaK B))
      ≤ 0 := by
    rw [← integral_add
      ((cΔπ.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self)
      ((cΔB.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ico_subset_Icc_self)]
    refine setIntegral_nonpos measurableSet_Ico fun s hs => ?_
    have ht : s - π ∈ Icc (π / 2 - θ) (π / 2) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h1 := hG.B_eq (s - π) ht
    have h2 := hBle (s - π) ⟨by linarith [ht.1], ht.2⟩
    rw [show π + (s - π) = s by ring] at h1 h2
    linarith
  have n2 : (∫ s in Ioc (3 * π / 2) (3 * π / 2 + θ),
        (supportFn K' (s - π) - supportFn K (s - π)) ∂(sigmaK D))
      + (∫ s in Ioc (3 * π / 2) (3 * π / 2 + θ), (supportFn D' s - supportFn D s) ∂(sigmaK D))
      ≤ 0 := by
    rw [← integral_add
      ((cΔπ.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self)
      ((cΔD.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self)]
    refine setIntegral_nonpos measurableSet_Ioc fun s hs => ?_
    have ht : s - 3 * π / 2 ∈ Icc 0 θ := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h1 := hG.D_eq (s - 3 * π / 2) ht
    have h2 := hDle (s - 3 * π / 2) ⟨ht.1, by linarith [ht.2]⟩
    rw [show π / 2 + (s - 3 * π / 2) = s - π by ring,
      show 3 * π / 2 + (s - 3 * π / 2) = s by ring] at h1 h2
    linarith
  unfold dirQ
  rw [s1, s2, s3, s4, s5, s6, s7]
  linarith

/-- **Baek Corollary 8.5.8** (abstract form): a triple with Gerver's structure maximizes `𝒬` on
`𝓛` (Thm 8.5.7 with Thm 8.5.6, the concavity Thm 8.3.8 and Thm 7.1.5). -/
theorem GerverData.Qfun_le (hG : GerverData φ θ K B D) (hP' : InL φ K' B' D') :
    Qfun φ K' B' D' ≤ Qfun φ K B D :=
  Qfun_le_of_dirQ_nonpos hG.phi_pos (hG.phi_lt_theta.trans hG.theta_lt) hG.cap
    hG.interior_nonempty hG.B_compact hG.B_nonempty hG.D_compact hG.D_nonempty hG.leq hG.X_B
    hG.Y_D hP' (hG.dirQ_nonpos hP'.injective.isCap hP'.B_compact hP'.B_nonempty hP'.D_compact
      hP'.D_nonempty hP'.B_le hP'.D_le)

end Sofa
