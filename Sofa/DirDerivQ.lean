/-
# Sofa/DirDerivQ.lean — Baek §8.5 (general part): the directional derivative of `𝒬`

Baek's §8.5 computes the directional derivative `D𝒬(P; P*)` of the upper bound
`𝒬(K, B, D) = |K| + J(d_D) + J(Y_D, x^L_K) − J(x_K|_{[φ, π/2−φ]}) + J(x^R_K, X_B) + J(b_B)`
along Minkowski segments `P_λ = c_λ(P, P*)` (Theorems 8.5.1–8.5.6) and, with the concavity of
Theorem 8.3.8 (`Qfun_concave`), turns "`D𝒬(P; ·) ≤ 0`" into "`P` maximizes `𝒬`" (Thm 7.1.5,
Cor 8.5.8).  Nothing here depends on Gerver's sofa.

* **The mixed closed form** (`integral_Ioc_supportFn_sigmaK`): for compact nonempty `A`, `B`,

      ∫_{(a,b]} h_A dσ_B = h_A(b) e⁺_B(b) − h_A(a) e⁺_B(a) + ∫_a^b (h_A h_B − e⁺_A e⁺_B),

  by integration by parts against `σ_B = d(arcFn B)` and then against `dt` — the polarization of
  `two_mul_curveG_eq`.  Consequences: the mixed area `V(A, B) = ½∫_{S¹} h_A dσ_B` is symmetric
  (`areaB_comm`), and `B(A, B) − B(B, A) = J(v⁻_A(b), v⁻_B(b)) − J(v⁺_A(a), v⁺_B(a))` for the
  convex-arc form of Lemma 7.3.3 (`convB_sub_convB`).
* **Quadratic expansions** of every term of `𝒬` along `P_λ` (Theorems 8.5.1–8.5.5).
* **Theorem 8.5.6** (`Qfun_le_add_dirQ`): if `X_B = x^R_K` and `Y_D = x^L_K`, then

      𝒬(P*) ≤ 𝒬(P) + D𝒬(P; P*),
      D𝒬(P; P*) = ⟨h_{K*} − h_K, σ_K⟩_{S¹} + ⟨h_{D*} − h_D, σ_D⟩_{(3π/2, 2π−φ)}
                   − ⟨h_{K*} − h_K, ι_K⟩_{I ∪ (I + π/2)} + ⟨h_{B*} − h_B, σ_B⟩_{(π+φ, 3π/2)}

  (the `≤` is the concavity of `𝒬`; `D𝒬` is the linear coefficient of the quadratic
  `λ ↦ 𝒬(P_λ)`), with `ι_K` the measure of Def 8.4.6, written with `e⁺ = h'` a.e.

STATUS: [PROOF-C-local] round 32 (2026-09-23, Opus 5.5).
-/
import Sofa.NicheCore

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace Interval Pointwise

namespace Sofa

variable {A B : Set ℝ²}

/-! ## The mixed closed form -/

lemma intervalIntegrable_edgeMax_mul (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) (a b : ℝ) :
    IntervalIntegrable (fun t => edgeMax A t * edgeMax B t) volume a b := by
  obtain ⟨R, _, hR⟩ := exists_radius hA hAne
  obtain ⟨S, _, hS⟩ := exists_radius hB hBne
  refine intervalIntegrable_of_bdd ((measurable_edgeMax hA hAne).mul (measurable_edgeMax hB hBne))
    (C := R * S) (fun t => ?_) a b
  rw [Pi.mul_apply, abs_mul]
  exact mul_le_mul (abs_edgeMax_le hA hAne hR t) (abs_edgeMax_le hB hBne hS t) (abs_nonneg _)
    (le_trans (abs_nonneg _) (abs_edgeMax_le hA hAne hR t))

/-- **The mixed closed form** of `∫ h_A dσ_B`. -/
theorem integral_Ioc_supportFn_sigmaK (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Ioc a b, supportFn A t ∂(sigmaK B)
      = supportFn A b * edgeMax B b - supportFn A a * edgeMax B a
        + ∫ t in a..b, (supportFn A t * supportFn B t - edgeMax A t * edgeMax B t) := by
  have hcA := continuous_supportFn hA hAne
  have hcB := continuous_supportFn hB hBne
  have hacA := absolutelyContinuousOnInterval_supportFn hA hAne a b
  have hHac := absolutelyContinuousOnInterval_primitive_supportFn hB hBne a b
  have hdeA := ae_deriv_supportFn hA hAne
  have hHderiv : deriv (fun t => ∫ s in (0:ℝ)..t, supportFn B s) = supportFn B :=
    funext fun t => (hasDerivAt_primitive_supportFn hB hBne t).deriv
  have harc : ∀ t, arcFn B t = edgeMax B t + ∫ s in (0:ℝ)..t, supportFn B s := fun t => by
    have := edgeMax_eq_arcFn_sub B t; linarith
  -- Step 1: integration by parts against `σ_B = d(arcFn B)`
  have h1 : ∫ t in Ioc a b, supportFn A t ∂(sigmaK B)
      = supportFn A b * arcFn B b - supportFn A a * arcFn B a
        - ∫ s in a..b, deriv (supportFn A) s * arcFn B s := by
    have := integral_Ioc_stieltjes (arcSF hB hBne) hab hacA
    simp only [arcSF_apply] at this
    rw [sigmaK_eq hB hBne, this]
  -- Step 2: `h_A' = e⁺_A` a.e. and `arcFn B = e⁺_B + H_B`
  have h2 : ∫ s in a..b, deriv (supportFn A) s * arcFn B s
      = ∫ s in a..b, (edgeMax A s * edgeMax B s
          + edgeMax A s * ∫ r in (0:ℝ)..s, supportFn B r) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hdeA] with s hs _
    rw [hs, harc]; ring
  -- Step 3: `∫ e⁺_A H_B = [h_A H_B] − ∫ h_A h_B`
  have h3 : ∫ s in a..b, edgeMax A s * ∫ r in (0:ℝ)..s, supportFn B r
      = supportFn A b * (∫ r in (0:ℝ)..b, supportFn B r)
        - supportFn A a * (∫ r in (0:ℝ)..a, supportFn B r)
        - ∫ s in a..b, supportFn A s * supportFn B s := by
    have hibp := hHac.integral_mul_deriv_eq_deriv_mul hacA
    have e1 : ∫ s in a..b, edgeMax A s * ∫ r in (0:ℝ)..s, supportFn B r
        = ∫ s in a..b, (∫ r in (0:ℝ)..s, supportFn B r) * deriv (supportFn A) s := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hdeA] with s hs _
      rw [hs]; ring
    have e2 : ∫ s in a..b, deriv (fun t => ∫ r in (0:ℝ)..t, supportFn B r) s * supportFn A s
        = ∫ s in a..b, supportFn A s * supportFn B s := by
      rw [hHderiv]; congr 1; funext s; ring
    rw [e1, hibp, e2]; ring
  have hie := intervalIntegrable_edgeMax_mul hA hAne hB hBne a b
  have hieH : IntervalIntegrable
      (fun s => edgeMax A s * ∫ r in (0:ℝ)..s, supportFn B r) volume a b :=
    (intervalIntegrable_edgeMax hA hAne a b).mul_continuousOn
      (continuous_primitive_supportFn hB hBne).continuousOn
  have hihh : IntervalIntegrable (fun s => supportFn A s * supportFn B s) volume a b :=
    (hcA.mul hcB).intervalIntegrable a b
  rw [h1, h2, intervalIntegral.integral_add hie hieH, h3,
    intervalIntegral.integral_sub hihh hie, harc, harc]
  ring

/-- The open-interval version: remove the atom `h_A(b) σ_B({b})`. -/
theorem integral_Ioo_supportFn_sigmaK (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {a b : ℝ} (hab : a < b) :
    ∫ t in Ioo a b, supportFn A t ∂(sigmaK B)
      = supportFn A b * edgeMin B b - supportFn A a * edgeMax B a
        + ∫ t in a..b, (supportFn A t * supportFn B t - edgeMax A t * edgeMax B t) := by
  have hdisj : Disjoint (Ioo a b) {b} := Set.disjoint_singleton_right.2 fun h => lt_irrefl _ h.2
  have hunion : Ioc a b = Ioo a b ∪ {b} := (Ioo_union_right hab).symm
  have hint : IntegrableOn (supportFn A) (Ioc a b) (sigmaK B) :=
    integrableOn_supportFn_sigmaK' hA hAne B a b
  have hsplit : ∫ t in Ioc a b, supportFn A t ∂(sigmaK B)
      = (∫ t in Ioo a b, supportFn A t ∂(sigmaK B))
        + ∫ t in ({b} : Set ℝ), supportFn A t ∂(sigmaK B) := by
    rw [hunion, setIntegral_union hdisj (measurableSet_singleton b)
      (hint.mono_set Ioo_subset_Ioc_self)
      (hint.mono_set (Set.singleton_subset_iff.2 ⟨hab, le_rfl⟩))]
  have hatom : ∫ t in ({b} : Set ℝ), supportFn A t ∂(sigmaK B)
      = supportFn A b * edgeLength B b := by
    rw [integral_singleton, smul_eq_mul, Measure.real, sigmaK_singleton hB hBne,
      ENNReal.toReal_ofReal (edgeLength_nonneg hB hBne b), mul_comm]
  have h := integral_Ioc_supportFn_sigmaK hA hAne hB hBne hab.le
  rw [hsplit, hatom, edgeLength] at h
  linarith

/-- **The antisymmetric part of the convex-arc form** (Baek's proof of Thm 8.5.2):
`B(A, B) − B(B, A) = J(v⁻_A(b), v⁻_B(b)) − J(v⁺_A(a), v⁺_B(a))`. -/
theorem convB_sub_convB (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {a b : ℝ} (hab : a < b) :
    convB a b A B - convB a b B A
      = segJ (vtxM A b) (vtxM B b) - segJ (vtxP A a) (vtxP B a) := by
  have h1 := integral_Ioo_supportFn_sigmaK hA hAne hB hBne hab
  have h2 := integral_Ioo_supportFn_sigmaK hB hBne hA hAne hab
  have hsym : ∫ t in a..b, (supportFn B t * supportFn A t - edgeMax B t * edgeMax A t)
      = ∫ t in a..b, (supportFn A t * supportFn B t - edgeMax A t * edgeMax B t) := by
    congr 1; funext t; ring
  rw [hsym] at h2
  rw [convB, convB, h1, h2, segJ, segJ, vtxM, vtxM, vtxP, vtxP, cross_frame, cross_frame]
  ring

/-- **The mixed area is symmetric** (over a full turn the boundary terms cancel). -/
theorem areaB_comm (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) (t₀ : ℝ) : areaB t₀ A B = areaB t₀ B A := by
  have hle : t₀ ≤ t₀ + 2 * π := by linarith [pi_pos]
  have h1 := integral_Ioc_supportFn_sigmaK hA hAne hB hBne hle
  have h2 := integral_Ioc_supportFn_sigmaK hB hBne hA hAne hle
  have hsym : ∫ t in t₀..t₀ + 2 * π, (supportFn B t * supportFn A t - edgeMax B t * edgeMax A t)
      = ∫ t in t₀..t₀ + 2 * π, (supportFn A t * supportFn B t - edgeMax A t * edgeMax B t) := by
    congr 1; funext t; ring
  rw [hsym] at h2
  rw [areaB, areaB, h1, h2, supportFn_add_two_pi, supportFn_add_two_pi, edgeMax_add_two_pi,
    edgeMax_add_two_pi]
  ring

/-! ## Quadratic expansions along Minkowski segments (Theorems 8.5.1–8.5.5) -/

/-- `v⁻_K(t)` is convex-linear in `K` (Thm 7.1.2 (2), left vertex). -/
theorem vtxM_mix (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (t : ℝ) :
    vtxM (mix l A B) t = (1 - l) • vtxM A t + l • vtxM B t := by
  have hM := isCompact_mix (l := l) hA hB
  have hMne := nonempty_mix (l := l) hAne hBne
  have h1 := tendsto_vtx2_left hM hMne t
  have h2 : Tendsto (fun s => vtx2 (mix l A B) s t) (𝓝[<] t)
      (𝓝 ((1 - l) • vtxM A t + l • vtxM B t)) := by
    have hA' := (tendsto_vtx2_left hA hAne t).const_smul (1 - l)
    have hB' := (tendsto_vtx2_left hB hBne t).const_smul l
    refine (hA'.add hB').congr fun s => ?_
    exact (vtx2_mix hA hAne hB hBne hl0 hl1 s t).symm
  exact tendsto_nhds_unique h1 h2

/-- **Theorem 8.5.3** (the expansion): `J` of a segment with convex-linear endpoints. -/
lemma segJ_mix_expand (p p' q q' : ℝ²) (l : ℝ) :
    segJ ((1 - l) • p + l • p') ((1 - l) • q + l • q')
      = (1 - l) ^ 2 * segJ p q + l * (1 - l) * (segJ p q' + segJ p' q)
        + l ^ 2 * segJ p' q' := by
  simp only [segJ, cross_add_left, cross_add_right, cross_smul_left, cross_smul_right]
  ring

/-- **Theorem 8.5.1** (the expansion): `|c_λ(A, B)| = (1−λ)²|A| + 2λ(1−λ) V(B, A) + λ²|B|`. -/
theorem volumeReal_mix_expand (hA : IsCompact A) (hAc : Convex ℝ A)
    (hAi : (interior A).Nonempty) (hB : IsCompact B) (hBc : Convex ℝ B)
    (hBi : (interior B).Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (t₀ : ℝ) :
    volume.real (mix l A B)
      = (1 - l) ^ 2 * volume.real A + l * (1 - l) * (2 * areaB t₀ B A)
        + l ^ 2 * volume.real B := by
  have hAne : A.Nonempty := hAi.mono interior_subset
  have hBne : B.Nonempty := hBi.mono interior_subset
  rw [volumeReal_eq_curveG_of_interior_nonempty (isCompact_mix hA hB) (convex_mix hAc hBc)
      (interior_mix_nonempty hAi hBi hl0 hl1) t₀,
    volumeReal_eq_curveG_of_interior_nonempty hA hAc hAi t₀,
    volumeReal_eq_curveG_of_interior_nonempty hB hBc hBi t₀, ← areaB_self, ← areaB_self,
    ← areaB_self, areaB_mix_left hA hAne hB hBne hl0 hl1,
    areaB_mix_right hA hAne hA hAne hB hBne hl0 hl1,
    areaB_mix_right hB hBne hA hAne hB hBne hl0 hl1, areaB_comm hA hAne hB hBne t₀]
  ring

/-- **Theorem 8.5.1** (the linear coefficient): `2V(B, A) − 2|A| = ∫_{S¹} (h_B − h_A) dσ_A`. -/
theorem two_mul_areaB_sub (hA : IsCompact A) (hAc : Convex ℝ A) (hAi : (interior A).Nonempty)
    (hB : IsCompact B) (hBne : B.Nonempty) (t₀ : ℝ) :
    2 * areaB t₀ B A - 2 * volume.real A
      = ∫ t in Ioc t₀ (t₀ + 2 * π), (supportFn B t - supportFn A t) ∂(sigmaK A) := by
  have hAne : A.Nonempty := hAi.mono interior_subset
  rw [volumeReal_eq_curveG_of_interior_nonempty hA hAc hAi t₀, ← areaB_self, areaB, areaB,
    integral_sub (integrableOn_supportFn_sigmaK' hB hBne A _ _)
      (integrableOn_supportFn_sigmaK' hA hAne A _ _)]
  ring

/-- **Theorem 8.5.2** (the expansion). -/
theorem convJ_mix_expand (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (a b : ℝ) :
    convJ (mix l A B) a b
      = (1 - l) ^ 2 * convJ A a b + l * (1 - l) * (convB a b A B + convB a b B A)
        + l ^ 2 * convJ B a b := by
  rw [← convB_self, ← convB_self, ← convB_self, convB_mix_left hA hAne hB hBne hl0 hl1,
    convB_mix_right hA hAne hA hAne hB hBne hl0 hl1,
    convB_mix_right hB hBne hA hAne hB hBne hl0 hl1]
  ring

/-- **Theorem 8.5.2** (the linear coefficient):
`B(A,B) + B(B,A) − 2J(u^{a,b}_A) = ∫_{(a,b)} (h_B − h_A) dσ_A + J(v⁻_A(b), v⁻_B(b)) − J(v⁺_A(a), v⁺_B(a))`. -/
theorem convB_add_convB_sub (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {a b : ℝ} (hab : a < b) :
    convB a b A B + convB a b B A - 2 * convJ A a b
      = (∫ t in Ioo a b, (supportFn B t - supportFn A t) ∂(sigmaK A))
        + (segJ (vtxM A b) (vtxM B b) - segJ (vtxP A a) (vtxP B a)) := by
  have h := convB_sub_convB hA hAne hB hBne hab
  have i1 := (integrableOn_supportFn_sigmaK' hB hBne A a b).mono_set Ioo_subset_Ioc_self
  have i2 := (integrableOn_supportFn_sigmaK' hA hAne A a b).mono_set Ioo_subset_Ioc_self
  have e1 : convB a b B A = (∫ t in Ioo a b, supportFn B t ∂(sigmaK A)) / 2 := rfl
  have e2 : convJ A a b = (∫ t in Ioo a b, supportFn A t ∂(sigmaK A)) / 2 := rfl
  rw [integral_sub i1 i2]
  linarith

/-! ### The inner corner curve -/

lemma ae_deriv_supportFn_add (hA : IsCompact A) (hAne : A.Nonempty) (c : ℝ) :
    ∀ᵐ t ∂volume, deriv (fun s => supportFn A (s + c)) t = edgeMax A (t + c) := by
  have hcount : ((fun t : ℝ => t + c) ⁻¹' {s : ℝ | edgeLength A s ≠ 0}).Countable :=
    (countable_edgeLength_ne_zero hA hAne).preimage (add_left_injective c)
  filter_upwards [hcount.ae_notMem volume] with t ht
  have h0 : edgeLength A (t + c) = 0 := by
    by_contra hc
    exact ht (by simpa using hc)
  rw [deriv_comp_add_const, (hasDerivAt_supportFn_of_edgeLength_eq_zero hA hAne h0).deriv]

lemma intervalIntegrable_edgeMax_add (hA : IsCompact A) (hAne : A.Nonempty) (c p q : ℝ) :
    IntervalIntegrable (fun t => edgeMax A (t + c)) volume p q := by
  have h := (intervalIntegrable_edgeMax hA hAne (p + c) (q + c)).comp_add_right c
  simpa using h

lemma intervalIntegrable_mul_edgeMax (hA : IsCompact A) (hAne : A.Nonempty) {f : ℝ → ℝ}
    (hf : Continuous f) (p q : ℝ) :
    IntervalIntegrable (fun t => f t * edgeMax A t) volume p q :=
  (intervalIntegrable_edgeMax hA hAne p q).continuousOn_mul hf.continuousOn

lemma intervalIntegrable_mul_edgeMax_add (hA : IsCompact A) (hAne : A.Nonempty) {f : ℝ → ℝ}
    (hf : Continuous f) (c p q : ℝ) :
    IntervalIntegrable (fun t => f t * edgeMax A (t + c)) volume p q :=
  (intervalIntegrable_edgeMax_add hA hAne c p q).continuousOn_mul hf.continuousOn

/-- `J(x_K)` in closed form: with `g = h_K(· + π/2)`,
`2 J(x_K|_{[p,q]}) = ∫_p^q ((h − 1)² + (g − 1)² + (h − 1) e⁺(· + π/2) − (g − 1) e⁺)`. -/
theorem two_mul_curveJ_innerCorner (hA : IsCompact A) (hAne : A.Nonempty) (p q : ℝ) :
    2 * curveJ (innerCorner A) p q
      = ∫ t in p..q, ((supportFn A t - 1) ^ 2 + (supportFn A (t + π / 2) - 1) ^ 2
          + (supportFn A t - 1) * edgeMax A (t + π / 2)
          - (supportFn A (t + π / 2) - 1) * edgeMax A t) := by
  have hh1 : AbsolutelyContinuousOnInterval (fun t => supportFn A t - 1) p q :=
    (absolutelyContinuousOnInterval_supportFn hA hAne p q).fun_sub (ac_const 1 p q)
  have hg1 : AbsolutelyContinuousOnInterval (fun t => supportFn A (t + π / 2) - 1) p q :=
    (ac_supportFn_add hA hAne (π / 2) p q).fun_sub (ac_const 1 p q)
  have hX := two_mul_curveJ_frame hh1 hg1
  have eX : innerCorner A
      = fun t => (supportFn A t - 1) • u t + (supportFn A (t + π / 2) - 1) • v t := rfl
  rw [← eX] at hX
  simp only [deriv_sub_const] at hX
  rw [hX]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_deriv_supportFn hA hAne, ae_deriv_supportFn_add hA hAne (π / 2)]
    with t h1 h2 _
  rw [h1, h2]

/-- The symmetric bilinear form behind `J(x_K)` (polarization of `two_mul_curveJ_innerCorner`). -/
def cornerB (A B : Set ℝ²) (p q : ℝ) : ℝ :=
  (∫ t in p..q, (2 * ((supportFn A t - 1) * (supportFn B t - 1))
      + 2 * ((supportFn A (t + π / 2) - 1) * (supportFn B (t + π / 2) - 1))
      + (supportFn A t - 1) * edgeMax B (t + π / 2)
      + (supportFn B t - 1) * edgeMax A (t + π / 2)
      - (supportFn A (t + π / 2) - 1) * edgeMax B t
      - (supportFn B (t + π / 2) - 1) * edgeMax A t)) / 2

lemma intervalIntegrable_cornerF (hA : IsCompact A) (hAne : A.Nonempty) (p q : ℝ) :
    IntervalIntegrable (fun t => (supportFn A t - 1) ^ 2 + (supportFn A (t + π / 2) - 1) ^ 2
      + (supportFn A t - 1) * edgeMax A (t + π / 2)
      - (supportFn A (t + π / 2) - 1) * edgeMax A t) volume p q := by
  have hc := continuous_supportFn hA hAne
  have hc' : Continuous fun t => supportFn A (t + π / 2) := hc.comp (continuous_add_const _)
  exact ((((hc.sub continuous_const).pow 2).add ((hc'.sub continuous_const).pow 2)
    ).intervalIntegrable p q |>.add
      (intervalIntegrable_mul_edgeMax_add hA hAne (hc.sub continuous_const) _ p q)).sub
    (intervalIntegrable_mul_edgeMax hA hAne (hc'.sub continuous_const) p q)

lemma intervalIntegrable_cornerG (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) (p q : ℝ) :
    IntervalIntegrable (fun t => 2 * ((supportFn A t - 1) * (supportFn B t - 1))
      + 2 * ((supportFn A (t + π / 2) - 1) * (supportFn B (t + π / 2) - 1))
      + (supportFn A t - 1) * edgeMax B (t + π / 2)
      + (supportFn B t - 1) * edgeMax A (t + π / 2)
      - (supportFn A (t + π / 2) - 1) * edgeMax B t
      - (supportFn B (t + π / 2) - 1) * edgeMax A t) volume p q := by
  have hcA := continuous_supportFn hA hAne
  have hcA' : Continuous fun t => supportFn A (t + π / 2) := hcA.comp (continuous_add_const _)
  have hcB := continuous_supportFn hB hBne
  have hcB' : Continuous fun t => supportFn B (t + π / 2) := hcB.comp (continuous_add_const _)
  exact (((((((hcA.sub continuous_const).mul (hcB.sub continuous_const)).const_smul (2:ℝ)).add
    (((hcA'.sub continuous_const).mul (hcB'.sub continuous_const)).const_smul (2:ℝ))
    ).intervalIntegrable p q |>.add
      (intervalIntegrable_mul_edgeMax_add hB hBne (hcA.sub continuous_const) _ p q)).add
      (intervalIntegrable_mul_edgeMax_add hA hAne (hcB.sub continuous_const) _ p q)).sub
      (intervalIntegrable_mul_edgeMax hB hBne (hcA'.sub continuous_const) p q)).sub
      (intervalIntegrable_mul_edgeMax hA hAne (hcB'.sub continuous_const) p q)

/-- **Theorem 8.5.4/8.5.5** (the expansion): `J(x_K)` is quadratic along Minkowski segments. -/
theorem curveJ_innerCorner_mix_expand (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (p q : ℝ) :
    curveJ (innerCorner (mix l A B)) p q
      = (1 - l) ^ 2 * curveJ (innerCorner A) p q + l * (1 - l) * cornerB A B p q
        + l ^ 2 * curveJ (innerCorner B) p q := by
  have eM := two_mul_curveJ_innerCorner (isCompact_mix (l := l) hA hB)
    (nonempty_mix (l := l) hAne hBne) p q
  have eA := two_mul_curveJ_innerCorner hA hAne p q
  have eB := two_mul_curveJ_innerCorner hB hBne p q
  have iA := intervalIntegrable_cornerF hA hAne p q
  have iB := intervalIntegrable_cornerF hB hBne p q
  have iG := intervalIntegrable_cornerG hA hAne hB hBne p q
  have hs := fun t => supportFn_mix hA hAne hB hBne hl0 hl1 t
  have he := fun t => edgeMax_mix hA hAne hB hBne hl0 hl1 t
  simp only [hs, he] at eM
  have hpt : ∀ t : ℝ,
      ((1 - l) * supportFn A t + l * supportFn B t - 1) ^ 2
        + ((1 - l) * supportFn A (t + π / 2) + l * supportFn B (t + π / 2) - 1) ^ 2
        + ((1 - l) * supportFn A t + l * supportFn B t - 1)
          * ((1 - l) * edgeMax A (t + π / 2) + l * edgeMax B (t + π / 2))
        - ((1 - l) * supportFn A (t + π / 2) + l * supportFn B (t + π / 2) - 1)
          * ((1 - l) * edgeMax A t + l * edgeMax B t)
      = (1 - l) ^ 2 * ((supportFn A t - 1) ^ 2 + (supportFn A (t + π / 2) - 1) ^ 2
          + (supportFn A t - 1) * edgeMax A (t + π / 2)
          - (supportFn A (t + π / 2) - 1) * edgeMax A t)
        + l * (1 - l) * (2 * ((supportFn A t - 1) * (supportFn B t - 1))
          + 2 * ((supportFn A (t + π / 2) - 1) * (supportFn B (t + π / 2) - 1))
          + (supportFn A t - 1) * edgeMax B (t + π / 2)
          + (supportFn B t - 1) * edgeMax A (t + π / 2)
          - (supportFn A (t + π / 2) - 1) * edgeMax B t
          - (supportFn B (t + π / 2) - 1) * edgeMax A t)
        + l ^ 2 * ((supportFn B t - 1) ^ 2 + (supportFn B (t + π / 2) - 1) ^ 2
          + (supportFn B t - 1) * edgeMax B (t + π / 2)
          - (supportFn B (t + π / 2) - 1) * edgeMax B t) := fun t => by ring
  simp only [hpt] at eM
  rw [intervalIntegral.integral_add ((iA.const_mul _).add (iG.const_mul _)) (iB.const_mul _),
    intervalIntegral.integral_add (iA.const_mul _) (iG.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, ← eA, ← eB] at eM
  rw [cornerB]
  linarith

/-- The density of Baek's measure `ι_K` (Def 8.4.6) on `(0, π/2]`: `i_K(t) = ⟪x_K'(t), v_t⟫`
`= h_K(t) − 1 + h_K'(t + π/2)`, written with `h_K' = e⁺_K` (a.e.). -/
def iotaV (K : Set ℝ²) (t : ℝ) : ℝ := supportFn K t - 1 + edgeMax K (t + π / 2)

/-- The density of `ι_K` on `(π/2, π]`: `i_K(t + π/2) = −⟪x_K'(t), u_t⟫ = h_K(t + π/2) − 1 − h_K'(t)`. -/
def iotaU (K : Set ℝ²) (t : ℝ) : ℝ := supportFn K (t + π / 2) - 1 - edgeMax K t

/-- **Theorem 8.5.5** (the linear coefficient):
`B(x_A, x_B) − 2J(x_A) = ⟨h_B − h_A, ι_A⟩_{[p,q] ∪ ([p,q] + π/2)} + J(x_A(q), x_B(q)) − J(x_A(p), x_B(p))`,
by integration by parts. -/
theorem cornerB_sub_two_mul_curveJ (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) (p q : ℝ) :
    cornerB A B p q - 2 * curveJ (innerCorner A) p q
      = (∫ t in p..q, ((supportFn B t - supportFn A t) * iotaV A t
          + (supportFn B (t + π / 2) - supportFn A (t + π / 2)) * iotaU A t))
        + (segJ (innerCorner A q) (innerCorner B q)
          - segJ (innerCorner A p) (innerCorner B p)) := by
  have hcA := continuous_supportFn hA hAne
  have hcA' : Continuous fun t => supportFn A (t + π / 2) := hcA.comp (continuous_add_const _)
  have hcB := continuous_supportFn hB hBne
  have hcB' : Continuous fun t => supportFn B (t + π / 2) := hcB.comp (continuous_add_const _)
  have eA := two_mul_curveJ_innerCorner hA hAne p q
  have iA := intervalIntegrable_cornerF hA hAne p q
  have iG := intervalIntegrable_cornerG hA hAne hB hBne p q
  -- the `ι` integrand
  have iV : IntervalIntegrable (iotaV A) volume p q :=
    ((hcA.sub continuous_const).intervalIntegrable p q).add
      (intervalIntegrable_edgeMax_add hA hAne _ p q)
  have iU : IntervalIntegrable (iotaU A) volume p q :=
    ((hcA'.sub continuous_const).intervalIntegrable p q).sub
      (intervalIntegrable_edgeMax hA hAne p q)
  have iT : IntervalIntegrable (fun t => (supportFn B t - supportFn A t) * iotaV A t
      + (supportFn B (t + π / 2) - supportFn A (t + π / 2)) * iotaU A t) volume p q :=
    (iV.continuousOn_mul (hcB.sub hcA).continuousOn).add
      (iU.continuousOn_mul (hcB'.sub hcA').continuousOn)
  -- integration by parts for the two products `α_A β_B` and `β_A α_B`
  have acA : AbsolutelyContinuousOnInterval (fun t => supportFn A t - 1) p q :=
    (absolutelyContinuousOnInterval_supportFn hA hAne p q).fun_sub (ac_const 1 p q)
  have acA' : AbsolutelyContinuousOnInterval (fun t => supportFn A (t + π / 2) - 1) p q :=
    (ac_supportFn_add hA hAne (π / 2) p q).fun_sub (ac_const 1 p q)
  have acB : AbsolutelyContinuousOnInterval (fun t => supportFn B t - 1) p q :=
    (absolutelyContinuousOnInterval_supportFn hB hBne p q).fun_sub (ac_const 1 p q)
  have acB' : AbsolutelyContinuousOnInterval (fun t => supportFn B (t + π / 2) - 1) p q :=
    (ac_supportFn_add hB hBne (π / 2) p q).fun_sub (ac_const 1 p q)
  have ibp1 := acA.integral_deriv_mul_eq_sub acB'
  have ibp2 := acA'.integral_deriv_mul_eq_sub acB
  simp only [deriv_sub_const] at ibp1 ibp2
  have hP1 : ∫ t in p..q, (edgeMax A t * (supportFn B (t + π / 2) - 1)
        + (supportFn A t - 1) * edgeMax B (t + π / 2))
      = (supportFn A q - 1) * (supportFn B (q + π / 2) - 1)
        - (supportFn A p - 1) * (supportFn B (p + π / 2) - 1) := by
    rw [← ibp1]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_deriv_supportFn hA hAne, ae_deriv_supportFn_add hB hBne (π / 2)]
      with t h1 h2 _
    rw [h1, h2]
  have hP2 : ∫ t in p..q, (edgeMax A (t + π / 2) * (supportFn B t - 1)
        + (supportFn A (t + π / 2) - 1) * edgeMax B t)
      = (supportFn A (q + π / 2) - 1) * (supportFn B q - 1)
        - (supportFn A (p + π / 2) - 1) * (supportFn B p - 1) := by
    rw [← ibp2]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [ae_deriv_supportFn_add hA hAne (π / 2), ae_deriv_supportFn hB hBne]
      with t h1 h2 _
    rw [h1, h2]
  have iP1 : IntervalIntegrable (fun t => edgeMax A t * (supportFn B (t + π / 2) - 1)
      + (supportFn A t - 1) * edgeMax B (t + π / 2)) volume p q :=
    ((intervalIntegrable_edgeMax hA hAne p q).mul_continuousOn
      (hcB'.sub continuous_const).continuousOn).add
      (intervalIntegrable_mul_edgeMax_add hB hBne (hcA.sub continuous_const) _ p q)
  have iP2 : IntervalIntegrable (fun t => edgeMax A (t + π / 2) * (supportFn B t - 1)
      + (supportFn A (t + π / 2) - 1) * edgeMax B t) volume p q :=
    ((intervalIntegrable_edgeMax_add hA hAne _ p q).mul_continuousOn
      (hcB.sub continuous_const).continuousOn).add
      (intervalIntegrable_mul_edgeMax hB hBne (hcA'.sub continuous_const) p q)
  -- the pointwise identity `G − 2F_A − 2T = P₁ − P₂`
  have hpt : ∀ t : ℝ,
      (2 * ((supportFn A t - 1) * (supportFn B t - 1))
        + 2 * ((supportFn A (t + π / 2) - 1) * (supportFn B (t + π / 2) - 1))
        + (supportFn A t - 1) * edgeMax B (t + π / 2)
        + (supportFn B t - 1) * edgeMax A (t + π / 2)
        - (supportFn A (t + π / 2) - 1) * edgeMax B t
        - (supportFn B (t + π / 2) - 1) * edgeMax A t)
      - 2 * ((supportFn A t - 1) ^ 2 + (supportFn A (t + π / 2) - 1) ^ 2
        + (supportFn A t - 1) * edgeMax A (t + π / 2)
        - (supportFn A (t + π / 2) - 1) * edgeMax A t)
      - 2 * ((supportFn B t - supportFn A t) * iotaV A t
        + (supportFn B (t + π / 2) - supportFn A (t + π / 2)) * iotaU A t)
      = (edgeMax A t * (supportFn B (t + π / 2) - 1)
          + (supportFn A t - 1) * edgeMax B (t + π / 2))
        - (edgeMax A (t + π / 2) * (supportFn B t - 1)
          + (supportFn A (t + π / 2) - 1) * edgeMax B t) := fun t => by
    rw [iotaV, iotaU]; ring
  have hint := intervalIntegral.integral_congr (μ := volume) (a := p) (b := q) (fun t _ => hpt t)
  rw [intervalIntegral.integral_sub (iG.sub (iA.const_mul 2)) (iT.const_mul 2),
    intervalIntegral.integral_sub iG (iA.const_mul 2), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub iP1 iP2, hP1, hP2,
    ← eA] at hint
  rw [cornerB, segJ, segJ, innerCorner, innerCorner, innerCorner, innerCorner, cross_frame,
    cross_frame]
  linarith

/-! ## Theorem 8.5.6: the directional derivative of `𝒬` -/

variable {φ : ℝ} {K D K' B' D' : Set ℝ²}

/-- **Baek Thm 8.5.6**: the directional derivative `D𝒬(P; P')` of `𝒬` at `P = (K, B, D)` towards
`P' = (K', B', D')`, for `P` with `X_B = x^R_K` and `Y_D = x^L_K`:

    ⟨h_{K'} − h_K, σ_K⟩_{S¹} + ⟨h_{D'} − h_D, σ_D⟩_{(3π/2, 2π−φ)}
      − ⟨h_{K'} − h_K, ι_K⟩_{I ∪ (I + π/2)} + ⟨h_{B'} − h_B, σ_B⟩_{(π+φ, 3π/2)},   I = [φ, π/2 − φ].

(Baek writes the `B`- and `D`-terms with `σ̆_B(X) = σ_B(X + π)` and `h̆_B(t) = h_B(t + π)` over
`(φ, π/2)` and `(π/2, π/2 + φ^L)`; this is the same after the shift by `π`.) -/
def dirQ (φ : ℝ) (K B D K' B' D' : Set ℝ²) : ℝ :=
  (∫ t in Ioc 0 (2 * π), (supportFn K' t - supportFn K t) ∂(sigmaK K))
    + (∫ t in Ioo (3 * π / 2) (2 * π - φ), (supportFn D' t - supportFn D t) ∂(sigmaK D))
    - (∫ t in φ..(π / 2 - φ), ((supportFn K' t - supportFn K t) * iotaV K t
        + (supportFn K' (t + π / 2) - supportFn K (t + π / 2)) * iotaU K t))
    + (∫ t in Ioo (π + φ) (3 * π / 2), (supportFn B' t - supportFn B t) ∂(sigmaK B))

/-- **Baek Theorem 8.5.6, with the concavity of `𝒬`** (Thm 8.3.8): if `X_B = x^R_K` and
`Y_D = x^L_K`, then `𝒬(P') ≤ 𝒬(P) + D𝒬(P; P')`.

`λ ↦ 𝒬(P_λ)` is a quadratic polynomial (Theorems 8.5.1–8.5.5) whose linear coefficient is
`D𝒬(P; P')` (the boundary terms telescope, and vanish at the two ends on the floor);
concavity at `λ = 1/2` makes its quadratic coefficient `≤ 0`. -/
theorem Qfun_le_add_dirQ (hφ0 : 0 < φ) (hφ1 : φ < π / 4) (hK : IsCap K (π / 2))
    (hK' : IsCap K' (π / 2)) (hi : (interior K).Nonempty) (hi' : (interior K').Nonempty)
    (hB : IsCompact B) (hBne : B.Nonempty) (hB' : IsCompact B') (hB'ne : B'.Nonempty)
    (hD : IsCompact D) (hDne : D.Nonempty) (hD' : IsCompact D') (hD'ne : D'.Nonempty)
    (hL : LEq φ K B D) (hL' : LEq φ K' B' D')
    (hXB : vtxP B (π + φ) = innerCorner K φ)
    (hYD : vtxM D (2 * π - φ) = innerCorner K (π / 2 - φ)) :
    Qfun φ K' B' D' ≤ Qfun φ K B D + dirQ φ K B D K' B' D' := by
  have hpi := pi_pos
  have hKc := hK.isCompact
  have hKne := hK.nonempty
  have hK'c := hK'.isCompact
  have hK'ne := hK'.nonempty
  have hl0 : (0:ℝ) ≤ 1 / 2 := by norm_num
  have hl1 : (1:ℝ) / 2 ≤ 1 := by norm_num
  have hconc := Qfun_concave hφ0 hφ1 hK hK' hi hi' hB hBne hB' hB'ne hD hDne hD' hD'ne hL hL'
    hl0 hl1
  -- the expansions at `λ = 1/2`
  have e1 := volumeReal_mix_expand hKc hK.convex hi hK'c hK'.convex hi' hl0 hl1 0
  have e2 := convJ_mix_expand hD hDne hD' hD'ne hl0 hl1 (3 * π / 2) (2 * π - φ)
  have e3 := segJ_mix_expand (vtxM D (2 * π - φ)) (vtxM D' (2 * π - φ))
    (innerCorner K (π / 2 - φ)) (innerCorner K' (π / 2 - φ)) (1 / 2)
  have e4 := curveJ_innerCorner_mix_expand hKc hKne hK'c hK'ne hl0 hl1 φ (π / 2 - φ)
  have e5 := segJ_mix_expand (innerCorner K φ) (innerCorner K' φ) (vtxP B (π + φ))
    (vtxP B' (π + φ)) (1 / 2)
  have e6 := convJ_mix_expand hB hBne hB' hB'ne hl0 hl1 (π + φ) (3 * π / 2)
  rw [← vtxM_mix hD hDne hD' hD'ne hl0 hl1, ← innerCorner_mix hKc hKne hK'c hK'ne hl0 hl1] at e3
  rw [← innerCorner_mix hKc hKne hK'c hK'ne hl0 hl1, ← vtxP_mix hB hBne hB' hB'ne hl0 hl1] at e5
  norm_num at e1 e2 e3 e4 e5 e6
  -- the linear coefficients
  have c1 := two_mul_areaB_sub hKc hK.convex hi hK'c hK'ne 0
  rw [zero_add] at c1
  have c2 := convB_add_convB_sub hD hDne hD' hD'ne (a := 3 * π / 2) (b := 2 * π - φ)
    (by linarith)
  have c4 := cornerB_sub_two_mul_curveJ hKc hKne hK'c hK'ne φ (π / 2 - φ)
  have c6 := convB_add_convB_sub hB hBne hB' hB'ne (a := π + φ) (b := 3 * π / 2) (by linarith)
  -- the ends on the floor
  have hB0 : supportFn B (3 * π / 2) = 0 := by linarith [hL.B_top, hK.supportFn_pi_div_two]
  have hB'0 : supportFn B' (3 * π / 2) = 0 := by linarith [hL'.B_top, hK'.supportFn_pi_div_two]
  have hD0 : supportFn D (3 * π / 2) = 0 := by linarith [hL.D_top, hK.supportFn_pi_div_two]
  have hD'0 : supportFn D' (3 * π / 2) = 0 := by linarith [hL'.D_top, hK'.supportFn_pi_div_two]
  have z1 : segJ (vtxP D (3 * π / 2)) (vtxP D' (3 * π / 2)) = 0 :=
    segJ_eq_zero_of_line_zero (by rw [inner_vtxP_u, hD0]) (by rw [inner_vtxP_u, hD'0])
  have z2 : segJ (vtxM B (3 * π / 2)) (vtxM B' (3 * π / 2)) = 0 :=
    segJ_eq_zero_of_line_zero (by rw [inner_vtxM_u, hB0]) (by rw [inner_vtxM_u, hB'0])
  -- the matching ends `Y_D = x^L_K`, `X_B = x^R_K`
  have f1 : segJ (vtxM D (2 * π - φ)) (vtxM D' (2 * π - φ))
      = -segJ (vtxM D' (2 * π - φ)) (innerCorner K (π / 2 - φ)) := by
    rw [hYD, segJ_comm]
  have f2 : segJ (vtxM D (2 * π - φ)) (innerCorner K' (π / 2 - φ))
      = segJ (innerCorner K (π / 2 - φ)) (innerCorner K' (π / 2 - φ)) := by rw [hYD]
  have f3 : segJ (vtxM D (2 * π - φ)) (innerCorner K (π / 2 - φ)) = 0 := by
    rw [hYD, segJ_self]
  have f4 : segJ (innerCorner K φ) (vtxP B (π + φ)) = 0 := by rw [hXB, segJ_self]
  have f5 : segJ (vtxP B (π + φ)) (vtxP B' (π + φ))
      = segJ (innerCorner K φ) (vtxP B' (π + φ)) := by rw [hXB]
  have f6 : segJ (innerCorner K' φ) (vtxP B (π + φ))
      = -segJ (innerCorner K φ) (innerCorner K' φ) := by rw [hXB, segJ_comm]
  unfold Qfun at hconc ⊢
  unfold dirQ
  norm_num at hconc
  linarith

/-! ## Corollary 8.5.8 (abstract form) -/

/-- A convex planar set of positive area has nonempty interior. -/
lemma interior_nonempty_of_volume_ne_zero {S : Set ℝ²} (hS : Convex ℝ S) (h : volume S ≠ 0) :
    (interior S).Nonempty := by
  rw [hS.interior_nonempty_iff_affineSpan_eq_top]
  by_contra hspan
  exact h (measure_mono_null (subset_affineSpan ℝ S)
    (Measure.addHaar_affineSubspace volume _ hspan))

/-- Every cap in `𝓛` has nonempty interior (its area is `≥ 2.2`). -/
lemma InL.interior_nonempty (hP : InL φ K B D) : (interior K).Nonempty := by
  refine interior_nonempty_of_volume_ne_zero hP.injective.isCap.convex fun h0 => ?_
  have h := hP.area
  rw [measureReal_def, h0, ENNReal.toReal_zero] at h
  norm_num at h

/-- **Baek Corollary 8.5.8** (abstract form, with Theorem 7.1.5 and Theorem 8.3.8): if the
directional derivative of `𝒬` at `P = (K, B, D)` (with matching ends `X_B = x^R_K`,
`Y_D = x^L_K`) is nonpositive towards `P' ∈ 𝓛`, then `𝒬(P') ≤ 𝒬(P)`. -/
theorem Qfun_le_of_dirQ_nonpos (hφ0 : 0 < φ) (hφ1 : φ < π / 4) (hK : IsCap K (π / 2))
    (hi : (interior K).Nonempty) (hB : IsCompact B) (hBne : B.Nonempty) (hD : IsCompact D)
    (hDne : D.Nonempty) (hL : LEq φ K B D) (hXB : vtxP B (π + φ) = innerCorner K φ)
    (hYD : vtxM D (2 * π - φ) = innerCorner K (π / 2 - φ)) (hP' : InL φ K' B' D')
    (hdir : dirQ φ K B D K' B' D' ≤ 0) :
    Qfun φ K' B' D' ≤ Qfun φ K B D := by
  have h := Qfun_le_add_dirQ hφ0 hφ1 hK hP'.injective.isCap hi hP'.interior_nonempty hB hBne
    hP'.B_compact hP'.B_nonempty hD hDne hP'.D_compact hP'.D_nonempty hL hP'.eq hXB hYD
  linarith

end Sofa
