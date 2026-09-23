/-
# Sofa/GerverODE.lean — Baek Prop 8.4.4 and Thm 8.4.5: Romik's ODEs as measure identities

Baek translates Romik's ten ODEs (Thm 8.4.2) for the boundary curves `A, B, C, D, x` of Gerver's
sofa into equalities of measures (Thm 8.4.5), using Thm 8.4.1 (1) (`A = A_K = v⁺_K`,
`C = C_K = v⁺_K(· + π/2)`, `x = x_K`) and Prop 8.4.4: on an interval where a vertex curve is
differentiable, the surface area measure has density `⟨A'(t), v_t⟩`.

* `sigmaK_Ioc_toReal_eq_integral` (Prop 8.4.4): if `c = v⁺_C(α + ·)` on `[a, b]`, `c` is
  continuous there with right derivatives `c'`, then `σ_C((α + a, α + b]) = ∫_a^b ⟪c', v_{α+s}⟫`
  (the fundamental theorem of calculus for `arcFn C = ⟪v⁺_C, v⟫ + ∫h_C`, whose derivative is
  `⟪c', v⟫` because `⟪v⁺_C(t), u_t⟫ = h_C(t)`).
* `restrict_Ico_eq_of_Ioc`, `restrict_Ioc_eq_of_Ioc`: two measures agreeing on the subintervals
  `(a, b]` of a piece agree on the piece.
* `GerverODE` (Thm 8.4.1 (1) + Thm 8.4.2): the vertex curves of `K` are differentiable away from
  the breakpoints `t₁, …, t₄`, and satisfy Romik's ODEs on `I₁, …, I₅`.
* `GerverODE.sigma_left`, `GerverODE.sigma_right` (**Thm 8.4.5**, grouped): the two measure
  identities of `GerverData`.

STATUS: [PROOF-C-local] round 35 (2026-09-23, Opus 5.5).
-/
import Sofa.GerverFaces

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace Interval

namespace Sofa

variable {K : Set ℝ²} {φ θ : ℝ} {Bc Dc : ℝ → ℝ²}

/-! ## Measures that agree on subintervals -/

/-- Two measures that agree on every `(a, b]` with `p ≤ a < b ≤ q` agree on `(p, q]`. -/
theorem restrict_Ioc_eq_of_Ioc {μ ν : Measure ℝ} [IsLocallyFiniteMeasure μ] {p q : ℝ}
    (h : ∀ a b, p ≤ a → a < b → b ≤ q → μ (Ioc a b) = ν (Ioc a b)) :
    μ.restrict (Ioc p q) = ν.restrict (Ioc p q) := by
  refine Measure.ext_of_Ioc _ _ fun a b hab => ?_
  rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc]
  have e : Ioc a b ∩ Ioc p q = Ioc (max a p) (min b q) := by
    ext x
    simp only [mem_inter_iff, mem_Ioc, max_lt_iff, le_min_iff]
    tauto
  rw [e]
  rcases lt_or_ge (max a p) (min b q) with hlt | hge
  · exact h _ _ (le_max_right _ _) hlt (min_le_right _ _)
  · rw [Ioc_eq_empty_of_le hge, measure_empty, measure_empty]

/-- Two measures with the same mass at `p` that agree on every `(a, b]` with `p ≤ a < b < q`
agree on `[p, q)`. -/
theorem restrict_Ico_eq_of_Ioc {μ ν : Measure ℝ} [IsLocallyFiniteMeasure μ] {p q : ℝ}
    (hp : μ {p} = ν {p}) (h : ∀ a b, p ≤ a → a < b → b < q → μ (Ioc a b) = ν (Ioc a b)) :
    μ.restrict (Ico p q) = ν.restrict (Ico p q) := by
  rcases le_or_gt q p with hqp | hpq
  · rw [Ico_eq_empty (not_lt.2 hqp), Measure.restrict_empty, Measure.restrict_empty]
  set c : ℕ → ℝ := fun n => q - (q - p) / ((n : ℝ) + 2) with hc
  have hcq : ∀ n, c n < q := fun n => by
    have : 0 < (q - p) / ((n : ℝ) + 2) := div_pos (by linarith) (by positivity)
    simp only [hc]; linarith
  have hU : Ico p q = {p} ∪ ⋃ n, Ioc p (c n) := by
    ext x
    simp only [mem_Ico, mem_union, mem_singleton_iff, mem_iUnion, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h1 with h | h
      · exact Or.inl h.symm
      · right
        have hqx : 0 < q - x := by linarith
        obtain ⟨n, hn⟩ := exists_nat_gt ((q - p) / (q - x))
        refine ⟨n, h, ?_⟩
        have hn' : q - p < n * (q - x) := (div_lt_iff₀ hqx).1 hn
        have : (q - p) / ((n : ℝ) + 2) ≤ q - x := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith
        simp only [hc]; linarith
    · rintro (h | ⟨n, h1, h2⟩)
      · subst h; exact ⟨le_rfl, hpq⟩
      · exact ⟨h1.le, lt_of_le_of_lt h2 (hcq n)⟩
  rw [hU, Measure.restrict_union_congr, Measure.restrict_iUnion_congr]
  refine ⟨by rw [Measure.restrict_singleton, Measure.restrict_singleton, hp], fun n => ?_⟩
  exact restrict_Ioc_eq_of_Ioc fun a b ha hab hb => h a b ha hab (lt_of_le_of_lt hb (hcq n))

/-! ## Prop 8.4.4: the density of `σ_C` along a differentiable vertex curve -/

/-- **Baek Prop 8.4.4** (general form): if `c = v⁺_C(α + ·)` on `[a, b]`, `c` is continuous on
`[a, b]` with right derivatives `c'` on `(a, b)`, and `⟪c', v_{α+·}⟫` is integrable, then
`σ_C((α + a, α + b]) = ∫_a^b ⟪c'(s), v_{α+s}⟫ ds`. -/
theorem sigmaK_Ioc_toReal_eq_integral {C : Set ℝ²} (hC : IsCompact C) (hne : C.Nonempty)
    {α a b : ℝ} (hab : a ≤ b) {c c' : ℝ → ℝ²} (hc : ∀ s ∈ Icc a b, c s = vtxP C (α + s))
    (hcont : ContinuousOn c (Icc a b))
    (hderiv : ∀ s ∈ Ioo a b, HasDerivWithinAt c (c' s) (Ioi s) s)
    (hint : IntervalIntegrable (fun s => ⟪c' s, v (α + s)⟫) volume a b) :
    (sigmaK C (Ioc (α + a) (α + b))).toReal = ∫ s in a..b, ⟪c' s, v (α + s)⟫ := by
  rw [sigmaK_Ioc_toReal hC hne (by linarith)]
  set F : ℝ → ℝ := fun s => ⟪c s, v (α + s)⟫ + ∫ r in (0:ℝ)..(α + s), supportFn C r with hF
  have hFa : F a = arcFn C (α + a) := by simp only [hF, arcFn, hc a ⟨le_rfl, hab⟩]
  have hFb : F b = arcFn C (α + b) := by simp only [hF, arcFn, hc b ⟨hab, le_rfl⟩]
  rw [← hFa, ← hFb]
  symm
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab ?_ (fun s hs => ?_) hint
  · refine (hcont.inner (continuous_v.comp (continuous_const.add continuous_id)).continuousOn).add
      ?_
    exact ((continuous_primitive_supportFn hC hne).comp
      (continuous_const.add continuous_id)).continuousOn
  · have hs' : s ∈ Icc a b := Ioo_subset_Icc_self hs
    have h1 : HasDerivWithinAt (fun r => v (α + r)) (-u (α + s)) (Ioi s) s :=
      ((hasDerivAt_v (α + s)).comp_const_add α s).hasDerivWithinAt
    have h2 := (hderiv s hs).inner (𝕜 := ℝ) h1
    have h3 : HasDerivWithinAt (fun r => ∫ x in (0:ℝ)..(α + r), supportFn C x)
        (supportFn C (α + s)) (Ioi s) s :=
      (((continuous_supportFn hC hne).integral_hasStrictDerivAt 0 (α + s)).hasDerivAt.comp_const_add
        α s).hasDerivWithinAt
    convert h2.add h3 using 1
    · rfl
    · rw [inner_neg_right, hc s hs', inner_vtxP_u]
      ring

/-- `σ̆_C((a, b]) = σ_C((a + π, b + π])`. -/
lemma sigmaBreve_Ioc (C : Set ℝ²) (a b : ℝ) :
    sigmaBreve C (Ioc a b) = sigmaK C (Ioc (a + π) (b + π)) := by
  rw [sigmaBreve, Measure.map_apply (measurable_sub_const π) measurableSet_Ioc,
    Set.preimage_sub_const_Ioc]

/-- `σ̆_C({a}) = σ_C({a + π})`. -/
lemma sigmaBreve_singleton (C : Set ℝ²) (a : ℝ) :
    sigmaBreve C {a} = sigmaK C {a + π} := by
  rw [sigmaBreve, Measure.map_apply (measurable_sub_const π) (measurableSet_singleton a)]
  congr 1
  ext x
  simp only [mem_preimage, mem_singleton_iff]
  constructor <;> intro h <;> linarith

/-- `ι_K((a, b]) = ∫_a^b i_K` where `i_K ≥ 0`. -/
lemma iotaK_Ioc {a b : ℝ} (hab : a ≤ b) (hint : IntervalIntegrable (iotaDens K) volume a b)
    (hnn : ∀ t ∈ Ioo a b, 0 ≤ iotaDens K t) :
    iotaK K (Ioc a b) = ENNReal.ofReal (∫ t in a..b, iotaDens K t) := by
  rw [iotaK, withDensity_apply _ measurableSet_Ioc, ← setLIntegral_congr Ioo_ae_eq_Ioc,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    ofReal_integral_eq_lintegral_ofReal (hint.1.mono_set Ioo_subset_Ioc_self)
      ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => hnn t ht)]

lemma iotaK_singleton (K : Set ℝ²) (a : ℝ) : iotaK K {a} = 0 := by
  rw [iotaK, withDensity_apply _ (measurableSet_singleton a), Measure.restrict_singleton,
    Real.volume_singleton, zero_smul, lintegral_zero_measure]

lemma intervalIntegrable_iotaV (hK : IsCompact K) (hne : K.Nonempty) (a b : ℝ) :
    IntervalIntegrable (iotaV K) volume a b := by
  have h := (intervalIntegrable_edgeMax hK hne (a + π / 2) (b + π / 2)).comp_add_right (π / 2)
  rw [add_sub_cancel_right, add_sub_cancel_right] at h
  exact (((continuous_supportFn hK hne).intervalIntegrable a b).sub intervalIntegrable_const).add h

lemma intervalIntegrable_iotaU (hK : IsCompact K) (hne : K.Nonempty) (a b : ℝ) :
    IntervalIntegrable (iotaU K) volume a b :=
  ((((continuous_supportFn hK hne).comp (continuous_add_const (π / 2))).intervalIntegrable
    a b).sub intervalIntegrable_const).sub (intervalIntegrable_edgeMax hK hne a b)

lemma v_add_pi' (t : ℝ) : v (t + π) = -v t := by
  rw [show t + π = t + π / 2 + π / 2 by ring, v_add_pi_div_two, u_add_pi_div_two]

/-! ## Continuity of the vertex curve where there is no edge -/

lemma continuousAt_vtxP_of_edgeLength_eq_zero (hK : IsCompact K) (hne : K.Nonempty) {t : ℝ}
    (h : edgeLength K t = 0) : ContinuousAt (vtxP K) t := by
  have hPM : vtxM K t = vtxP K t := by
    have := vtxP_sub_vtxM K t
    rw [h, zero_smul, sub_eq_zero] at this
    exact this.symm
  refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
  · rw [← continuousWithinAt_Iio_iff_Iic]
    have := tendsto_vtxP_left hK hne t
    rw [hPM] at this
    exact this
  · rw [← continuousWithinAt_Ioi_iff_Ici]
    exact tendsto_vtxP_right hK hne t

lemma IsInjectiveCap.continuousAt_vtxP_left (hK : IsInjectiveCap K) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < π / 2) : ContinuousAt (vtxP K) t :=
  continuousAt_vtxP_of_edgeLength_eq_zero hK.isCap.isCompact hK.isCap.nonempty
    (hK.edgeLength_eq_zero_left ht0 ht)

lemma IsInjectiveCap.continuousAt_vtxP_right (hK : IsInjectiveCap K) {t : ℝ} (ht0 : π / 2 < t)
    (ht : t ≤ π) : ContinuousAt (vtxP K) t :=
  continuousAt_vtxP_of_edgeLength_eq_zero hK.isCap.isCompact hK.isCap.nonempty
    (hK.edgeLength_eq_zero_right ht0 ht)

/-! ## Prop 8.4.4 for the cap and for the tails -/

/-- **Baek Prop 8.4.4 (1)**: on `[a, b] ⊆ [0, π/2)`, if `A_K = v⁺_K` is differentiable on
`(a, b)`, then `σ_K((a, b]) = ∫_a^b ⟪A_K', v_t⟫`. -/
theorem IsInjectiveCap.sigmaK_Ioc_eq_left (hK : IsInjectiveCap K) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b < π / 2) (hdiff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ (vtxP K) t)
    (hint : IntervalIntegrable (fun t => ⟪deriv (vtxP K) t, v t⟫) volume a b) :
    sigmaK K (Ioc a b) = ENNReal.ofReal (∫ t in a..b, ⟪deriv (vtxP K) t, v t⟫) := by
  have hKc := hK.isCap.isCompact
  have hne := hK.isCap.nonempty
  have h := sigmaK_Ioc_toReal_eq_integral hKc hne (α := 0) hab (c := vtxP K)
    (c' := deriv (vtxP K)) (fun s _ => by rw [zero_add])
    (fun s hs => (hK.continuousAt_vtxP_left (ha.trans hs.1)
      (lt_of_le_of_lt hs.2 hb)).continuousWithinAt)
    (fun s hs => (hdiff s hs).hasDerivAt.hasDerivWithinAt)
    (by simpa only [zero_add] using hint)
  simp only [zero_add] at h
  rw [← h, ENNReal.ofReal_toReal (sigmaK_Ioc_ne_top hKc hne a b)]

/-- **Baek Prop 8.4.4 (3)**: on `[a, b] ⊆ [0, π/2]`, if `C_K = v⁺_K(· + π/2)` is differentiable
on `(a, b)`, then `σ_K((π/2 + a, π/2 + b]) = ∫_a^b ⟪−C_K', u_t⟫`. -/
theorem IsInjectiveCap.sigmaK_Ioc_eq_right (hK : IsInjectiveCap K) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ π / 2)
    (hdiff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ (vtxP K) (t + π / 2))
    (hint : IntervalIntegrable (fun t => ⟪deriv (vtxP K) (t + π / 2), u t⟫) volume a b) :
    sigmaK K (Ioc (π / 2 + a) (π / 2 + b))
      = ENNReal.ofReal (∫ t in a..b, ⟪-deriv (vtxP K) (t + π / 2), u t⟫) := by
  have hpi := pi_pos
  have hKc := hK.isCap.isCompact
  have hne := hK.isCap.nonempty
  have hcont : ContinuousOn (fun s => vtxP K (π / 2 + s)) (Icc a b) := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · subst h
      have h1 : ContinuousWithinAt (vtxP K) (Ici (π / 2 + a)) (π / 2 + a) :=
        continuousWithinAt_Ioi_iff_Ici.1 (tendsto_vtxP_right hKc hne _)
      exact h1.comp (continuous_const_add (π / 2)).continuousWithinAt
        (fun r hr => show π / 2 + a ≤ π / 2 + r by linarith [hr.1])
    · exact ((hK.continuousAt_vtxP_right (by linarith) (by linarith [hs.2])).comp
        (continuous_const_add (π / 2)).continuousAt).continuousWithinAt
  have e : ∀ s, ⟪deriv (vtxP K) (π / 2 + s), v (π / 2 + s)⟫
      = ⟪-deriv (vtxP K) (s + π / 2), u s⟫ := fun s => by
    rw [add_comm (π / 2) s, v_add_pi_div_two, inner_neg_right, inner_neg_left]
  have hint' : IntervalIntegrable (fun s => ⟪-deriv (vtxP K) (s + π / 2), u s⟫) volume a b :=
    hint.neg.congr fun s _ => by simp only [Pi.neg_apply, inner_neg_left]
  have h := sigmaK_Ioc_toReal_eq_integral hKc hne (α := π / 2) hab
    (c := fun s => vtxP K (π / 2 + s)) (c' := fun s => deriv (vtxP K) (π / 2 + s))
    (fun s _ => rfl) hcont (fun s hs => ?_) (by simp only [e]; exact hint')
  · simp only [e] at h
    rw [← h, ENNReal.ofReal_toReal (sigmaK_Ioc_ne_top hKc hne _ _)]
  · have hd := hdiff s hs
    rw [add_comm s] at hd
    exact (hd.hasDerivAt.comp_const_add (π / 2) s).hasDerivWithinAt

/-- **Baek Prop 8.4.4 (2)**: on `[a, b] ⊆ [t₃, t₅)`, `σ̆_{B_K}((a, b]) = ∫_a^b ⟪−B', v_t⟫ = ∫_a^b (−β)`
(Thm 8.4.3 (1): `B = v⁺_{B_K}(π + ·)` there). -/
theorem GerverTails.sigmaBreve_Ioc_B (hT : GerverTails φ θ K Bc Dc) {β : ℝ → ℝ}
    (hβ : ∀ t ∈ Ico (π / 2 - θ) (π / 2), β t < 0 ∧ HasDerivWithinAt Bc (β t • v t) (Ici t) t)
    {a b : ℝ} (ha : π / 2 - θ ≤ a) (hab : a ≤ b) (hb : b < π / 2)
    (hint : IntervalIntegrable β volume a b) :
    sigmaBreve (Bset φ K) (Ioc a b) = ENNReal.ofReal (∫ t in a..b, -β t) := by
  have hpi := pi_pos
  have hcap := hT.injective.isCap
  have hBc : IsCompact (Bset φ K) := isCompact_Bset hcap.isCompact
  have hBne : (Bset φ K).Nonempty := hcap.Bset_nonempty hT.phi_pos.le
  obtain ⟨-, hP, -, -, -⟩ := hcap.gerver_B_side hT.phi_pos hT.phi_lt_theta hT.theta_lt
    hT.B_cont hT.B_mem hT.B_wall hT.B_start
  have e : ∀ s, ⟪β s • v s, v (π + s)⟫ = -β s := fun s => by
    rw [real_inner_smul_left, add_comm π s, v_add_pi', inner_neg_right, inner_v_v]; ring
  have h := sigmaK_Ioc_toReal_eq_integral hBc hBne (α := π) hab (c := Bc)
    (c' := fun s => β s • v s) (fun s hs => hP s ⟨ha.trans hs.1, lt_of_le_of_lt hs.2 hb⟩)
    (hT.B_cont.mono (Icc_subset_Icc ha hb.le))
    (fun s hs => (hβ s ⟨by linarith [hs.1], by linarith [hs.2]⟩).2.mono Ioi_subset_Ici_self)
    (by simp only [e]; exact hint.neg)
  simp only [e] at h
  rw [sigmaBreve_Ioc, add_comm a π, add_comm b π, ← h,
    ENNReal.ofReal_toReal (sigmaK_Ioc_ne_top hBc hBne _ _)]

/-- **Baek Prop 8.4.4 (4)**: on `[a, b] ⊆ [t₀, t₂]`,
`σ̆_{D_K}((π/2 + a, π/2 + b]) = ∫_a^b ⟪D', u_t⟫ = ∫_a^b δ` (Thm 8.4.3 (1): `D = v^±_{D_K}(3π/2 + ·)`). -/
theorem GerverTails.sigmaBreve_Ioc_D (hT : GerverTails φ θ K Bc Dc) {δ : ℝ → ℝ}
    (hδ : ∀ t ∈ Ico 0 θ, 0 < δ t ∧ HasDerivWithinAt Dc (δ t • u t) (Ici t) t)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ θ)
    (hint : IntervalIntegrable δ volume a b) :
    sigmaBreve (Dset φ K) (Ioc (π / 2 + a) (π / 2 + b)) = ENNReal.ofReal (∫ t in a..b, δ t) := by
  have hpi := pi_pos
  have hφ0 := hT.phi_pos
  have hφθ := hT.phi_lt_theta
  have hθ := hT.theta_lt
  have hcap := hT.injective.isCap
  have hDc : IsCompact (Dset φ K) := isCompact_Dset hcap.isCompact
  have hDne : (Dset φ K).Nonempty := hcap.Dset_nonempty hφ0.le
  obtain ⟨-, hP, hM, -, hnull⟩ := hcap.gerver_D_side hφ0 hφθ hθ hT.D_cont hT.D_mem hT.D_wall
    hT.D_end
  -- at `t₂ = θ` the two vertices of `D_K` agree
  have hθPM : vtxP (Dset φ K) (3 * π / 2 + θ) = vtxM (Dset φ K) (3 * π / 2 + θ) := by
    have h0 : sigmaK (Dset φ K) {3 * π / 2 + θ} = 0 :=
      measure_mono_null (show {3 * π / 2 + θ} ⊆ Ico (3 * π / 2 + θ) (2 * π - φ) from
        singleton_subset_iff.2 ⟨le_rfl, by linarith⟩) hnull
    rw [sigmaK_singleton hDc hDne, ENNReal.ofReal_eq_zero] at h0
    have hl : edgeLength (Dset φ K) (3 * π / 2 + θ) = 0 :=
      le_antisymm h0 (edgeLength_nonneg hDc hDne _)
    have := vtxP_sub_vtxM (Dset φ K) (3 * π / 2 + θ)
    rw [hl, zero_smul, sub_eq_zero] at this
    exact this
  have hPD : ∀ s ∈ Icc a b, Dc s = vtxP (Dset φ K) (3 * π / 2 + s) := by
    intro s hs
    rcases eq_or_lt_of_le (hs.2.trans hb) with h | h
    · rw [h, hθPM]; exact hM θ ⟨by linarith, le_rfl⟩
    · exact hP s ⟨ha.trans hs.1, h⟩
  have e : ∀ s, ⟪δ s • u s, v (3 * π / 2 + s)⟫ = δ s := fun s => by
    rw [real_inner_smul_left, show 3 * π / 2 + s = s + π / 2 + π by ring, v_add_pi',
      v_add_pi_div_two, neg_neg, inner_u_u, mul_one]
  have h := sigmaK_Ioc_toReal_eq_integral hDc hDne (α := 3 * π / 2) hab (c := Dc)
    (c' := fun s => δ s • u s) hPD (hT.D_cont.mono (Icc_subset_Icc ha hb))
    (fun s hs => (hδ s ⟨by linarith [hs.1], by linarith [hs.2]⟩).2.mono Ioi_subset_Ici_self)
    (by simp only [e]; exact hint)
  simp only [e] at h
  rw [sigmaBreve_Ioc, show π / 2 + a + π = 3 * π / 2 + a by ring,
    show π / 2 + b + π = 3 * π / 2 + b by ring, ← h,
    ENNReal.ofReal_toReal (sigmaK_Ioc_ne_top hDc hDne _ _)]

/-- `ι_K` on the left half: `ι_K((a, b]) = ∫_a^b i_K` with `i_K = ⟪x_K', v⟫ = g_K − 1`. -/
lemma IsInjectiveCap.iotaK_Ioc_left (hK : IsInjectiveCap K) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b < π / 2) : iotaK K (Ioc a b) = ENNReal.ofReal (∫ t in a..b, iotaV K t) := by
  have hKc := hK.isCap.isCompact
  have hne := hK.isCap.nonempty
  have heq : EqOn (iotaV K) (iotaDens K) (Ioo a b) := fun t ht => by
    rw [iotaDens, if_pos (by linarith [ht.2])]
  rw [iotaK_Ioc hab ((intervalIntegrable_iotaV hKc hne a b).congr_uIoo (by rwa [uIoo_of_le hab]))
      fun t ht => ?_, intervalIntegral.integral_congr_Ioo_of_le hab heq.symm]
  rw [← heq ht, iotaV_eq]
  linarith [(hK.one_lt_arm t ⟨by linarith [ht.1], by linarith [ht.2]⟩).2]

/-- `ι_K` on the right half: `ι_K((π/2 + a, π/2 + b]) = ∫_a^b i_K(· + π/2)` with
`i_K(· + π/2) = ⟪−x_K', u⟫ = f_K − 1`. -/
lemma IsInjectiveCap.iotaK_Ioc_right (hK : IsInjectiveCap K) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ π / 2) :
    iotaK K (Ioc (π / 2 + a) (π / 2 + b)) = ENNReal.ofReal (∫ t in a..b, iotaU K t) := by
  have hKc := hK.isCap.isCompact
  have hne := hK.isCap.nonempty
  have hab' : π / 2 + a ≤ π / 2 + b := by linarith
  have heq : EqOn (fun t => iotaU K (t - π / 2)) (iotaDens K) (Ioo (π / 2 + a) (π / 2 + b)) :=
    fun t ht => by rw [iotaDens, if_neg (by linarith [ht.1])]
  have hint : IntervalIntegrable (fun t => iotaU K (t - π / 2)) volume (π / 2 + a) (π / 2 + b) := by
    have := (intervalIntegrable_iotaU hKc hne a b).comp_sub_right (π / 2)
    rwa [show a + π / 2 = π / 2 + a by ring, show b + π / 2 = π / 2 + b by ring] at this
  rw [iotaK_Ioc hab' (hint.congr_uIoo (by rwa [uIoo_of_le hab'])) fun t ht => ?_,
    ← intervalIntegral.integral_congr_Ioo_of_le hab' heq]
  · congr 1
    have := intervalIntegral.integral_comp_add_left (fun t => iotaU K (t - π / 2)) (a := a) (b := b)
      (π / 2)
    simp only [add_sub_cancel_left] at this
    exact this.symm
  · rw [← heq ht]
    show 0 ≤ iotaU K (t - π / 2)
    rw [iotaU_eq]
    linarith [(hK.one_lt_arm (t - π / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩).1]

/-! ## Romik's ODEs and Theorem 8.4.5 -/

/-- **Baek Thm 8.4.1 (1) + Thm 8.4.2** (Romik's ODEs, [Rom18] Thm 2), for the cap `K` of Gerver's
sofa, stated for the curves of `K` itself: by Thm 8.4.1 (1) Romik's `A`, `C`, `x` are the vertex
curves `A_K = v⁺_K`, `C_K = v⁺_K(· + π/2)` and the inner corner `x_K`; `B`, `D` are the tails
(`B'`, `D'` are right derivatives).  The intervals are `I₁ = [0, φ]`, `I₂ = [φ, θ]`,
`I₃ = [θ, π/2 − θ]`, `I₄ = [π/2 − θ, π/2 − φ]`, `I₅ = [π/2 − φ, π/2]` (Def 8.4.1).  The curves are
piecewise smooth (Def 8.4.3): `A_K`, `C_K` are differentiable away from the breakpoints, with
`⟪A_K', v⟫`, `⟪C_K', u⟫` integrable. -/
structure GerverODE (φ θ : ℝ) (K : Set ℝ²) (Bc Dc : ℝ → ℝ²) : Prop where
  A_diff : ∀ t ∈ Ioo 0 (π / 2), t ∉ ({φ, θ, π / 2 - θ, π / 2 - φ} : Set ℝ) →
    DifferentiableAt ℝ (vtxP K) t
  C_diff : ∀ t ∈ Ioo 0 (π / 2), t ∉ ({φ, θ, π / 2 - θ, π / 2 - φ} : Set ℝ) →
    DifferentiableAt ℝ (vtxP K) (t + π / 2)
  A_int : IntervalIntegrable (fun t => ⟪deriv (vtxP K) t, v t⟫) volume 0 (π / 2)
  C_int : IntervalIntegrable (fun t => ⟪deriv (vtxP K) (t + π / 2), u t⟫) volume 0 (π / 2)
  /-- (1)-v on `I₁` (contacts `A, C, D`), Romik (21) -/
  v1 : ∀ t ∈ Ioo 0 φ, ⟪deriv (vtxP K) t, v t⟫ = 0
  /-- (1)-u on `I₁`, Romik (22) -/
  u1 : ∀ t ∈ Ioo 0 φ, ⟪-deriv (vtxP K) (t + π / 2), u t⟫ = ⟪derivWithin Dc (Ici t) t, u t⟫
  /-- (2)-v on `I₂` (contacts `A, C, D, x`), Romik (17) -/
  v2 : ∀ t ∈ Ioo φ θ, ⟪deriv (vtxP K) t, v t⟫ = ⟪deriv (innerCorner K) t, v t⟫
  /-- (2)-u on `I₂`, Romik (19) -/
  u2 : ∀ t ∈ Ioo φ θ, ⟪-deriv (vtxP K) (t + π / 2), u t⟫
    = ⟪derivWithin Dc (Ici t) t - deriv (innerCorner K) t, u t⟫
  /-- (3)-v on `I₃` (contacts `A, C, x`), Romik (17) -/
  v3 : ∀ t ∈ Ioo θ (π / 2 - θ), ⟪deriv (vtxP K) t, v t⟫ = ⟪deriv (innerCorner K) t, v t⟫
  /-- (3)-u on `I₃`, Romik (18) -/
  u3 : ∀ t ∈ Ioo θ (π / 2 - θ),
    ⟪-deriv (vtxP K) (t + π / 2), u t⟫ = ⟪-deriv (innerCorner K) t, u t⟫
  /-- (4)-v on `I₄` (contacts `A, B, C, x`), Romik (20) -/
  v4 : ∀ t ∈ Ioo (π / 2 - θ) (π / 2 - φ),
    ⟪deriv (vtxP K) t, v t⟫ = ⟪-derivWithin Bc (Ici t) t + deriv (innerCorner K) t, v t⟫
  /-- (4)-u on `I₄`, Romik (18) -/
  u4 : ∀ t ∈ Ioo (π / 2 - θ) (π / 2 - φ),
    ⟪-deriv (vtxP K) (t + π / 2), u t⟫ = ⟪-deriv (innerCorner K) t, u t⟫
  /-- (5)-v on `I₅` (contacts `A, B, C`) -/
  v5 : ∀ t ∈ Ioo (π / 2 - φ) (π / 2), ⟪deriv (vtxP K) t, v t⟫ = ⟪-derivWithin Bc (Ici t) t, v t⟫
  /-- (5)-u on `I₅` -/
  u5 : ∀ t ∈ Ioo (π / 2 - φ) (π / 2), ⟪-deriv (vtxP K) (t + π / 2), u t⟫ = 0

lemma Ico_inter_Ico_eq_empty_of_le {a b c d : ℝ} (h : b ≤ c) : Ico a b ∩ Ico c d = ∅ :=
  eq_empty_of_forall_notMem fun x hx => by linarith [hx.1.2, hx.2.1]

lemma Ico_inter_Ico_eq_empty_of_le' {a b c d : ℝ} (h : d ≤ a) : Ico a b ∩ Ico c d = ∅ :=
  eq_empty_of_forall_notMem fun x hx => by linarith [hx.1.1, hx.2.2]

lemma Ioc_inter_Ioc_eq_empty_of_le {a b c d : ℝ} (h : b ≤ c) : Ioc a b ∩ Ioc c d = ∅ :=
  eq_empty_of_forall_notMem fun x hx => by linarith [hx.1.2, hx.2.1]

lemma Ioc_inter_Ioc_eq_empty_of_le' {a b c d : ℝ} (h : d ≤ a) : Ioc a b ∩ Ioc c d = ∅ :=
  eq_empty_of_forall_notMem fun x hx => by linarith [hx.1.1, hx.2.2]

/-- **Baek Theorem 8.4.5** (1)–(4), grouped: on `[0, π/2)`,
`σ_K = ι_K|_{[φ, π/2 − φ)} + σ̆_{B_K}|_{[t₃, π/2)}`. -/
theorem GerverODE.sigma_left (hO : GerverODE φ θ K Bc Dc) (hT : GerverTails φ θ K Bc Dc) :
    (sigmaK K).restrict (Ico 0 (π / 2))
      = (iotaK K).restrict (Ico φ (π / 2 - φ))
        + (sigmaBreve (Bset φ K)).restrict (Ico (π / 2 - θ) (π / 2)) := by
  have hpi := pi_pos
  have hφ0 := hT.phi_pos
  have hφθ := hT.phi_lt_theta
  have hθ := hT.theta_lt
  have hK := hT.injective
  have hcap := hK.isCap
  have hKc := hcap.isCompact
  have hne := hcap.nonempty
  have hBc : IsCompact (Bset φ K) := isCompact_Bset hKc
  have hBne : (Bset φ K).Nonempty := hcap.Bset_nonempty hφ0.le
  obtain ⟨-, hP, hM, -, hBnull⟩ := hcap.gerver_B_side hφ0 hφθ hθ hT.B_cont hT.B_mem hT.B_wall
    hT.B_start
  obtain ⟨β, hβ⟩ := hT.B_deriv
  have hBd : ∀ t ∈ Ico (π / 2 - θ) (π / 2), derivWithin Bc (Ici t) t = β t • v t :=
    fun t ht => (hβ t ht).2.derivWithin (uniqueDiffWithinAt_Ici t)
  have hxv : ∀ t ∈ Ioo 0 (π / 2), ⟪deriv (innerCorner K) t, v t⟫ = iotaV K t := fun t ht => by
    rw [(hK.hasDerivAt_innerCorner ht.1 ht.2).deriv, inner_add_smul_v_v, iotaV_eq]
  have hAint : ∀ a b, 0 ≤ a → a ≤ b → b ≤ π / 2 →
      IntervalIntegrable (fun t => ⟪deriv (vtxP K) t, v t⟫) volume a b := fun a b ha hab hb =>
    hO.A_int.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le (by linarith)]; exact Icc_subset_Icc ha hb)
  -- `σ_K((a, b]) = ∫_a^b ⟪A_K', v⟫` inside a piece `(p, q)` free of breakpoints
  have hσ : ∀ p q a b, 0 ≤ p → q ≤ π / 2 →
      (∀ t ∈ Ioo p q, t ≠ φ ∧ t ≠ θ ∧ t ≠ π / 2 - θ ∧ t ≠ π / 2 - φ) → p ≤ a → a < b → b < q →
      sigmaK K (Ioc a b) = ENNReal.ofReal (∫ t in a..b, ⟪deriv (vtxP K) t, v t⟫) := by
    intro p q a b hp hq hpc ha hab hb
    refine hK.sigmaK_Ioc_eq_left (hp.trans ha) hab.le (by linarith) (fun t ht => ?_)
      (hAint a b (hp.trans ha) hab.le (by linarith))
    have ht' : t ∈ Ioo p q := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨h1, h2, h3, h4⟩ := hpc t ht'
    exact hO.A_diff t ⟨by linarith [ht'.1], by linarith [ht'.2]⟩ (by
      simp only [mem_insert_iff, mem_singleton_iff, not_or]; exact ⟨h1, h2, h3, h4⟩)
  have hσ0 : ∀ t, 0 ≤ t → t < π / 2 → sigmaK K {t} = 0 := fun t h0 h1 => by
    rw [sigmaK_singleton hKc hne, hK.edgeLength_eq_zero_left h0 h1, ENNReal.ofReal_zero]
  have hVnn : ∀ a b, 0 < a → a ≤ b → b < π / 2 → 0 ≤ ∫ t in a..b, iotaV K t :=
    fun a b ha hab hb => intervalIntegral.integral_nonneg hab fun t ht => by
      rw [iotaV_eq]
      linarith [(hK.one_lt_arm t ⟨by linarith [ht.1], by linarith [ht.2]⟩).2]
  -- `J₁ = [0, φ)`: `σ_K = 0`
  have P1 : (sigmaK K).restrict (Ico 0 φ) = 0 := by
    have h := restrict_Ico_eq_of_Ioc (μ := sigmaK K) (ν := 0) (p := 0) (q := φ)
      (by rw [hσ0 0 le_rfl (by linarith), Measure.coe_zero, Pi.zero_apply])
      (fun a b ha hab hb => by
        have hz : ∫ t in a..b, ⟪deriv (vtxP K) t, v t⟫ = 0 := by
          rw [intervalIntegral.integral_congr_Ioo_of_le hab.le (g := fun _ => (0 : ℝ))
            (fun t ht => hO.v1 t ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
          simp
        rw [hσ 0 φ a b le_rfl (by linarith) (fun t ht => ⟨ne_of_lt ht.2,
          ne_of_lt (by linarith [ht.2]), ne_of_lt (by linarith [ht.2]),
          ne_of_lt (by linarith [ht.2])⟩) ha hab hb, hz, ENNReal.ofReal_zero, Measure.coe_zero,
          Pi.zero_apply])
    rwa [Measure.restrict_zero] at h
  -- `J₂ ∪ J₃`: `σ_K = ι_K` where `⟪A', v⟫ = ⟪x', v⟫`
  have Pι : ∀ p q, 0 < p → p < q → q ≤ π / 2 →
      (∀ t ∈ Ioo p q, t ≠ φ ∧ t ≠ θ ∧ t ≠ π / 2 - θ ∧ t ≠ π / 2 - φ) →
      (∀ t ∈ Ioo p q, ⟪deriv (vtxP K) t, v t⟫ = ⟪deriv (innerCorner K) t, v t⟫) →
      (sigmaK K).restrict (Ico p q) = (iotaK K).restrict (Ico p q) := by
    intro p q hp hpq hq hpc hode
    refine restrict_Ico_eq_of_Ioc (by rw [hσ0 p hp.le (by linarith), iotaK_singleton])
      fun a b ha hab hb => ?_
    rw [hσ p q a b hp.le hq hpc ha hab hb, hK.iotaK_Ioc_left (by linarith) hab.le (by linarith),
      intervalIntegral.integral_congr_Ioo_of_le hab.le (g := iotaV K) (fun t ht => by
        rw [hode t ⟨by linarith [ht.1], by linarith [ht.2]⟩,
          hxv t ⟨by linarith [ht.1], by linarith [ht.2]⟩])]
  have P2 := Pι φ θ hφ0 hφθ (by linarith) (fun t ht => ⟨ne_of_gt ht.1, ne_of_lt ht.2,
    ne_of_lt (by linarith [ht.2]), ne_of_lt (by linarith [ht.2])⟩) hO.v2
  have P3 := Pι θ (π / 2 - θ) (by linarith) (by linarith) (by linarith)
    (fun t ht => ⟨ne_of_gt (by linarith [ht.1]), ne_of_gt ht.1, ne_of_lt ht.2,
      ne_of_lt (by linarith [ht.2])⟩) hO.v3
  -- `J₄ = [t₃, t₄)`: `σ_K = σ̆_B + ι_K`
  have P4 : (sigmaK K).restrict (Ico (π / 2 - θ) (π / 2 - φ))
      = (iotaK K + sigmaBreve (Bset φ K)).restrict (Ico (π / 2 - θ) (π / 2 - φ)) := by
    refine restrict_Ico_eq_of_Ioc ?_ fun a b ha hab hb => ?_
    · rw [hσ0 _ (by linarith) (by linarith), Measure.add_apply, iotaK_singleton,
        sigmaBreve_singleton, zero_add]
      exact (measure_mono_null (show {π / 2 - θ + π} ⊆ Ioc (π + φ) (3 * π / 2 - θ) from
        singleton_subset_iff.2 ⟨by linarith, by linarith⟩) hBnull).symm
    · have hode : ∀ t ∈ Ioo a b, ⟪deriv (vtxP K) t, v t⟫ = -β t + iotaV K t := fun t ht => by
        have ht4 : t ∈ Ioo (π / 2 - θ) (π / 2 - φ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        rw [hO.v4 t ht4, hBd t ⟨ht4.1.le, by linarith [ht4.2]⟩, inner_add_left, inner_neg_left,
          real_inner_smul_left, inner_v_v, mul_one,
          hxv t ⟨by linarith [ht4.1], by linarith [ht4.2]⟩]
      have hβint : IntervalIntegrable β volume a b := by
        refine ((intervalIntegrable_iotaV hKc hne a b).sub
          (hAint a b (by linarith) hab.le (by linarith))).congr_uIoo ?_
        rw [uIoo_of_le hab.le]
        intro t ht
        simp only [hode t ht]
        ring
      have hβnn : 0 ≤ ∫ t in a..b, -β t := intervalIntegral.integral_nonneg hab.le fun t ht =>
        by linarith [(hβ t ⟨by linarith [ht.1], by linarith [ht.2]⟩).1]
      rw [hσ (π / 2 - θ) (π / 2 - φ) a b (by linarith) (by linarith)
          (fun t ht => ⟨ne_of_gt (by linarith [ht.1]), ne_of_gt (by linarith [ht.1]),
            ne_of_gt ht.1, ne_of_lt ht.2⟩) ha hab hb,
        Measure.add_apply, hK.iotaK_Ioc_left (by linarith) hab.le (by linarith),
        hT.sigmaBreve_Ioc_B hβ ha hab.le (by linarith) hβint,
        intervalIntegral.integral_congr_Ioo_of_le hab.le (g := fun t => -β t + iotaV K t) hode,
        intervalIntegral.integral_add (f := fun t => -β t) (g := iotaV K) hβint.neg
          (intervalIntegrable_iotaV hKc hne a b),
        ENNReal.ofReal_add hβnn (hVnn a b (by linarith) hab.le (by linarith)), add_comm]
  -- `J₅ = [t₄, π/2)`: `σ_K = σ̆_B`
  have P5 : (sigmaK K).restrict (Ico (π / 2 - φ) (π / 2))
      = (sigmaBreve (Bset φ K)).restrict (Ico (π / 2 - φ) (π / 2)) := by
    refine restrict_Ico_eq_of_Ioc ?_ fun a b ha hab hb => ?_
    · rw [hσ0 _ (by linarith) (by linarith), sigmaBreve_singleton, sigmaK_singleton hBc hBne,
        edgeLength, ← inner_vtxP_v, ← inner_vtxM_v, add_comm (π / 2 - φ) π,
        ← hP (π / 2 - φ) ⟨by linarith, by linarith⟩, ← hM (π / 2 - φ) ⟨by linarith, by linarith⟩,
        sub_self, ENNReal.ofReal_zero]
    · have hode : ∀ t ∈ Ioo a b, ⟪deriv (vtxP K) t, v t⟫ = -β t := fun t ht => by
        have ht5 : t ∈ Ioo (π / 2 - φ) (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        rw [hO.v5 t ht5, hBd t ⟨by linarith [ht5.1], ht5.2⟩, inner_neg_left, real_inner_smul_left,
          inner_v_v, mul_one]
      have hβint : IntervalIntegrable β volume a b := by
        refine (hAint a b (by linarith) hab.le (by linarith)).neg.congr_uIoo ?_
        rw [uIoo_of_le hab.le]
        intro t ht
        simp only [Pi.neg_apply, hode t ht, neg_neg]
      rw [hσ (π / 2 - φ) (π / 2) a b (by linarith) le_rfl
          (fun t ht => ⟨ne_of_gt (by linarith [ht.1]), ne_of_gt (by linarith [ht.1]),
            ne_of_gt (by linarith [ht.1]), ne_of_gt ht.1⟩) ha hab hb,
        hT.sigmaBreve_Ioc_B hβ (by linarith) hab.le hb hβint,
        intervalIntegral.integral_congr_Ioo_of_le hab.le (g := fun t => -β t) hode]
  -- assembly
  set ν := (iotaK K).restrict (Ico φ (π / 2 - φ))
    + (sigmaBreve (Bset φ K)).restrict (Ico (π / 2 - θ) (π / 2)) with hν
  have hνJ : ∀ J, MeasurableSet J → ν.restrict J = (iotaK K).restrict (J ∩ Ico φ (π / 2 - φ))
      + (sigmaBreve (Bset φ K)).restrict (J ∩ Ico (π / 2 - θ) (π / 2)) := fun J hJ => by
    rw [hν, Measure.restrict_add, Measure.restrict_restrict hJ, Measure.restrict_restrict hJ]
  have hνS : ν.restrict (Ico 0 (π / 2)) = ν := by
    rw [hνJ _ measurableSet_Ico, inter_eq_right.2 (Ico_subset_Ico hφ0.le (by linarith)),
      inter_eq_right.2 (Ico_subset_Ico (by linarith) le_rfl)]
  rw [← hνS]
  have hS : Ico 0 (π / 2) = Ico 0 φ ∪ (Ico φ θ ∪ (Ico θ (π / 2 - θ)
      ∪ (Ico (π / 2 - θ) (π / 2 - φ) ∪ Ico (π / 2 - φ) (π / 2)))) := by
    rw [Ico_union_Ico_eq_Ico (by linarith) (by linarith),
      Ico_union_Ico_eq_Ico (by linarith) (by linarith),
      Ico_union_Ico_eq_Ico (by linarith) (by linarith),
      Ico_union_Ico_eq_Ico (by linarith) (by linarith)]
  rw [hS, Measure.restrict_union_congr, Measure.restrict_union_congr,
    Measure.restrict_union_congr, Measure.restrict_union_congr]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hνJ _ measurableSet_Ico, Ico_inter_Ico_eq_empty_of_le le_rfl,
      Ico_inter_Ico_eq_empty_of_le (by linarith), Measure.restrict_empty, Measure.restrict_empty,
      add_zero, P1]
  · rw [hνJ _ measurableSet_Ico, inter_eq_left.2 (Ico_subset_Ico le_rfl (by linarith)),
      Ico_inter_Ico_eq_empty_of_le (by linarith), Measure.restrict_empty, add_zero, P2]
  · rw [hνJ _ measurableSet_Ico, inter_eq_left.2 (Ico_subset_Ico (by linarith) (by linarith)),
      Ico_inter_Ico_eq_empty_of_le le_rfl, Measure.restrict_empty, add_zero, P3]
  · rw [hνJ _ measurableSet_Ico, inter_eq_left.2 (Ico_subset_Ico (by linarith) le_rfl),
      inter_eq_left.2 (Ico_subset_Ico le_rfl (by linarith)), ← Measure.restrict_add, P4]
  · rw [hνJ _ measurableSet_Ico, Ico_inter_Ico_eq_empty_of_le' le_rfl,
      inter_eq_left.2 (Ico_subset_Ico (by linarith) le_rfl), Measure.restrict_empty, zero_add, P5]

/-- **Baek Theorem 8.4.5** (5)–(8), grouped: on `(π/2, π]`,
`σ_K = ι_K|_{(π/2 + φ, π − φ]} + σ̆_{D_K}|_{(π/2, π/2 + θ]}`. -/
theorem GerverODE.sigma_right (hO : GerverODE φ θ K Bc Dc) (hT : GerverTails φ θ K Bc Dc) :
    (sigmaK K).restrict (Ioc (π / 2) π)
      = (iotaK K).restrict (Ioc (π / 2 + φ) (π - φ))
        + (sigmaBreve (Dset φ K)).restrict (Ioc (π / 2) (π / 2 + θ)) := by
  have hpi := pi_pos
  have hφ0 := hT.phi_pos
  have hφθ := hT.phi_lt_theta
  have hθ := hT.theta_lt
  have hK := hT.injective
  have hcap := hK.isCap
  have hKc := hcap.isCompact
  have hne := hcap.nonempty
  obtain ⟨δ, hδ⟩ := hT.D_deriv
  have hDd : ∀ t ∈ Ico 0 θ, derivWithin Dc (Ici t) t = δ t • u t :=
    fun t ht => (hδ t ht).2.derivWithin (uniqueDiffWithinAt_Ici t)
  have hxu : ∀ t ∈ Ioo 0 (π / 2), ⟪-deriv (innerCorner K) t, u t⟫ = iotaU K t := fun t ht => by
    rw [(hK.hasDerivAt_innerCorner ht.1 ht.2).deriv, inner_neg_left, inner_add_smul_u_v, iotaU_eq]
    ring
  have hCint' : ∀ a b, 0 ≤ a → a ≤ b → b ≤ π / 2 →
      IntervalIntegrable (fun t => ⟪-deriv (vtxP K) (t + π / 2), u t⟫) volume a b :=
    fun a b ha hab hb => (hO.C_int.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le (by linarith)]; exact Icc_subset_Icc ha hb)).neg.congr
      fun s _ => by simp only [Pi.neg_apply, inner_neg_left]
  -- `σ_K((a', b'])` inside a piece `(π/2 + p, π/2 + q]`, in the variable `t − π/2`
  have hσ : ∀ p q a' b', 0 ≤ p → q ≤ π / 2 →
      (∀ t ∈ Ioo p q, t ≠ φ ∧ t ≠ θ ∧ t ≠ π / 2 - θ ∧ t ≠ π / 2 - φ) →
      π / 2 + p ≤ a' → a' < b' → b' ≤ π / 2 + q →
      sigmaK K (Ioc a' b') = ENNReal.ofReal
        (∫ t in (a' - π / 2)..(b' - π / 2), ⟪-deriv (vtxP K) (t + π / 2), u t⟫) := by
    intro p q a' b' hp hq hpc ha hab hb
    have h := hK.sigmaK_Ioc_eq_right (a := a' - π / 2) (b := b' - π / 2) (by linarith)
      (by linarith) (by linarith) (fun t ht => ?_)
      (hO.C_int.mono_set (by
        rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
        exact Icc_subset_Icc (by linarith) (by linarith)))
    · rwa [show π / 2 + (a' - π / 2) = a' by ring, show π / 2 + (b' - π / 2) = b' by ring] at h
    · have ht' : t ∈ Ioo p q := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      obtain ⟨h1, h2, h3, h4⟩ := hpc t ht'
      exact hO.C_diff t ⟨by linarith [ht'.1], by linarith [ht'.2]⟩ (by
        simp only [mem_insert_iff, mem_singleton_iff, not_or]; exact ⟨h1, h2, h3, h4⟩)
  have hιR : ∀ a' b', π / 2 ≤ a' → a' ≤ b' → b' ≤ π →
      iotaK K (Ioc a' b') = ENNReal.ofReal (∫ t in (a' - π / 2)..(b' - π / 2), iotaU K t) := by
    intro a' b' ha hab hb
    have h := hK.iotaK_Ioc_right (a := a' - π / 2) (b := b' - π / 2) (by linarith) (by linarith)
      (by linarith)
    rwa [show π / 2 + (a' - π / 2) = a' by ring, show π / 2 + (b' - π / 2) = b' by ring] at h
  have hDR : ∀ a' b', π / 2 ≤ a' → a' ≤ b' → b' ≤ π / 2 + θ →
      IntervalIntegrable δ volume (a' - π / 2) (b' - π / 2) →
      sigmaBreve (Dset φ K) (Ioc a' b')
        = ENNReal.ofReal (∫ t in (a' - π / 2)..(b' - π / 2), δ t) := by
    intro a' b' ha hab hb hint
    have h := hT.sigmaBreve_Ioc_D hδ (a := a' - π / 2) (b := b' - π / 2) (by linarith)
      (by linarith) (by linarith) hint
    rwa [show π / 2 + (a' - π / 2) = a' by ring, show π / 2 + (b' - π / 2) = b' by ring] at h
  have hUnn : ∀ a b, 0 < a → a ≤ b → b < π / 2 → 0 ≤ ∫ t in a..b, iotaU K t :=
    fun a b ha hab hb => intervalIntegral.integral_nonneg hab fun t ht => by
      rw [iotaU_eq]
      linarith [(hK.one_lt_arm t ⟨by linarith [ht.1], by linarith [ht.2]⟩).1]
  -- `J₆ = (π/2, π/2 + φ]`: `σ_K = σ̆_D`
  have Q1 : (sigmaK K).restrict (Ioc (π / 2) (π / 2 + φ))
      = (sigmaBreve (Dset φ K)).restrict (Ioc (π / 2) (π / 2 + φ)) := by
    refine restrict_Ioc_eq_of_Ioc fun a' b' ha hab hb => ?_
    have hode : ∀ t ∈ Ioo (a' - π / 2) (b' - π / 2),
        ⟪-deriv (vtxP K) (t + π / 2), u t⟫ = δ t := fun t ht => by
      have ht1 : t ∈ Ioo 0 φ := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      rw [hO.u1 t ht1, hDd t ⟨ht1.1.le, by linarith [ht1.2]⟩, real_inner_smul_left, inner_u_u,
        mul_one]
    have hδint : IntervalIntegrable δ volume (a' - π / 2) (b' - π / 2) := by
      refine (hCint' _ _ (by linarith) (by linarith) (by linarith)).congr_uIoo ?_
      rw [uIoo_of_le (by linarith)]
      exact hode
    rw [hσ 0 φ a' b' le_rfl (by linarith) (fun t ht => ⟨ne_of_lt ht.2,
        ne_of_lt (by linarith [ht.2]), ne_of_lt (by linarith [ht.2]),
        ne_of_lt (by linarith [ht.2])⟩) (by linarith) hab hb,
      hDR a' b' ha hab.le (by linarith) hδint,
      intervalIntegral.integral_congr_Ioo_of_le (by linarith) hode]
  -- `J₇ = (π/2 + φ, π/2 + θ]`: `σ_K = σ̆_D + ι_K`
  have Q2 : (sigmaK K).restrict (Ioc (π / 2 + φ) (π / 2 + θ))
      = (iotaK K + sigmaBreve (Dset φ K)).restrict (Ioc (π / 2 + φ) (π / 2 + θ)) := by
    refine restrict_Ioc_eq_of_Ioc fun a' b' ha hab hb => ?_
    have hode : ∀ t ∈ Ioo (a' - π / 2) (b' - π / 2),
        ⟪-deriv (vtxP K) (t + π / 2), u t⟫ = δ t + iotaU K t := fun t ht => by
      have ht2 : t ∈ Ioo φ θ := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      rw [hO.u2 t ht2, hDd t ⟨by linarith [ht2.1], ht2.2⟩, sub_eq_add_neg, inner_add_left,
        real_inner_smul_left, inner_u_u, mul_one, hxu t ⟨by linarith [ht2.1], by linarith [ht2.2]⟩]
    have hδint : IntervalIntegrable δ volume (a' - π / 2) (b' - π / 2) := by
      refine ((hCint' _ _ (by linarith) (by linarith) (by linarith)).sub
        (intervalIntegrable_iotaU hKc hne _ _)).congr_uIoo ?_
      rw [uIoo_of_le (by linarith)]
      intro t ht
      simp only [hode t ht]
      ring
    have hδnn : 0 ≤ ∫ t in (a' - π / 2)..(b' - π / 2), δ t := by
      rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
      exact setIntegral_nonneg measurableSet_Ioo fun t ht =>
        (hδ t ⟨by linarith [ht.1], by linarith [ht.2]⟩).1.le
    rw [hσ φ θ a' b' hφ0.le (by linarith) (fun t ht => ⟨ne_of_gt ht.1, ne_of_lt ht.2,
        ne_of_lt (by linarith [ht.2]), ne_of_lt (by linarith [ht.2])⟩) ha hab hb,
      Measure.add_apply, hιR a' b' (by linarith) hab.le (by linarith),
      hDR a' b' (by linarith) hab.le hb hδint,
      intervalIntegral.integral_congr_Ioo_of_le (by linarith) hode,
      intervalIntegral.integral_add hδint (intervalIntegrable_iotaU hKc hne _ _),
      ENNReal.ofReal_add hδnn (hUnn _ _ (by linarith) (by linarith) (by linarith)), add_comm]
  -- `J₈ ∪ J₉`: `σ_K = ι_K` where `⟪−C', u⟫ = ⟪−x', u⟫`
  have Qι : ∀ p q, 0 < p → p ≤ q → q < π / 2 →
      (∀ t ∈ Ioo p q, t ≠ φ ∧ t ≠ θ ∧ t ≠ π / 2 - θ ∧ t ≠ π / 2 - φ) →
      (∀ t ∈ Ioo p q, ⟪-deriv (vtxP K) (t + π / 2), u t⟫ = ⟪-deriv (innerCorner K) t, u t⟫) →
      (sigmaK K).restrict (Ioc (π / 2 + p) (π / 2 + q))
        = (iotaK K).restrict (Ioc (π / 2 + p) (π / 2 + q)) := by
    intro p q hp hpq hq hpc hode
    refine restrict_Ioc_eq_of_Ioc fun a' b' ha hab hb => ?_
    rw [hσ p q a' b' hp.le hq.le hpc ha hab hb, hιR a' b' (by linarith) hab.le (by linarith),
      intervalIntegral.integral_congr_Ioo_of_le (by linarith) (g := iotaU K) (fun t ht => by
        rw [hode t ⟨by linarith [ht.1], by linarith [ht.2]⟩,
          hxu t ⟨by linarith [ht.1], by linarith [ht.2]⟩])]
  have Q3 := Qι θ (π / 2 - θ) (by linarith) (by linarith) (by linarith)
    (fun t ht => ⟨ne_of_gt (by linarith [ht.1]), ne_of_gt ht.1, ne_of_lt ht.2,
      ne_of_lt (by linarith [ht.2])⟩) hO.u3
  have Q4 := Qι (π / 2 - θ) (π / 2 - φ) (by linarith) (by linarith) (by linarith)
    (fun t ht => ⟨ne_of_gt (by linarith [ht.1]), ne_of_gt (by linarith [ht.1]), ne_of_gt ht.1,
      ne_of_lt ht.2⟩) hO.u4
  rw [show π / 2 + (π / 2 - θ) = π - θ by ring] at Q3 Q4
  rw [show π / 2 + (π / 2 - φ) = π - φ by ring] at Q4
  -- `J₁₀ = (π − φ, π]`: `σ_K = 0`
  have Q5 : (sigmaK K).restrict (Ioc (π - φ) π) = 0 := by
    have h := restrict_Ioc_eq_of_Ioc (μ := sigmaK K) (ν := 0) (p := π - φ) (q := π)
      fun a' b' ha hab hb => by
        have hz : ∫ t in (a' - π / 2)..(b' - π / 2), ⟪-deriv (vtxP K) (t + π / 2), u t⟫ = 0 := by
          rw [intervalIntegral.integral_congr_Ioo_of_le (by linarith) (g := fun _ => (0 : ℝ))
            (fun t ht => hO.u5 t ⟨by linarith [ht.1], by linarith [ht.2]⟩)]
          simp
        rw [hσ (π / 2 - φ) (π / 2) a' b' (by linarith) le_rfl
            (fun t ht => ⟨ne_of_gt (by linarith [ht.1]), ne_of_gt (by linarith [ht.1]),
              ne_of_gt (by linarith [ht.1]), ne_of_gt ht.1⟩) (by linarith) hab (by linarith),
          hz, ENNReal.ofReal_zero, Measure.coe_zero, Pi.zero_apply]
    rwa [Measure.restrict_zero] at h
  -- assembly
  set ν := (iotaK K).restrict (Ioc (π / 2 + φ) (π - φ))
    + (sigmaBreve (Dset φ K)).restrict (Ioc (π / 2) (π / 2 + θ)) with hν
  have hνJ : ∀ J, MeasurableSet J → ν.restrict J = (iotaK K).restrict (J ∩ Ioc (π / 2 + φ) (π - φ))
      + (sigmaBreve (Dset φ K)).restrict (J ∩ Ioc (π / 2) (π / 2 + θ)) := fun J hJ => by
    rw [hν, Measure.restrict_add, Measure.restrict_restrict hJ, Measure.restrict_restrict hJ]
  have hνS : ν.restrict (Ioc (π / 2) π) = ν := by
    rw [hνJ _ measurableSet_Ioc, inter_eq_right.2 (Ioc_subset_Ioc (by linarith) (by linarith)),
      inter_eq_right.2 (Ioc_subset_Ioc le_rfl (by linarith))]
  rw [← hνS]
  have hS : Ioc (π / 2) π = Ioc (π / 2) (π / 2 + φ) ∪ (Ioc (π / 2 + φ) (π / 2 + θ)
      ∪ (Ioc (π / 2 + θ) (π - θ) ∪ (Ioc (π - θ) (π - φ) ∪ Ioc (π - φ) π))) := by
    rw [Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith),
      Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith),
      Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith),
      Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)]
  rw [hS, Measure.restrict_union_congr, Measure.restrict_union_congr,
    Measure.restrict_union_congr, Measure.restrict_union_congr]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hνJ _ measurableSet_Ioc, Ioc_inter_Ioc_eq_empty_of_le le_rfl,
      inter_eq_left.2 (Ioc_subset_Ioc le_rfl (by linarith)), Measure.restrict_empty, zero_add, Q1]
  · rw [hνJ _ measurableSet_Ioc, inter_eq_left.2 (Ioc_subset_Ioc le_rfl (by linarith)),
      inter_eq_left.2 (Ioc_subset_Ioc (by linarith) le_rfl), ← Measure.restrict_add, Q2]
  · rw [hνJ _ measurableSet_Ioc, inter_eq_left.2 (Ioc_subset_Ioc (by linarith) (by linarith)),
      Ioc_inter_Ioc_eq_empty_of_le' le_rfl, Measure.restrict_empty, add_zero, Q3]
  · rw [hνJ _ measurableSet_Ioc, inter_eq_left.2 (Ioc_subset_Ioc (by linarith) le_rfl),
      Ioc_inter_Ioc_eq_empty_of_le' (by linarith), Measure.restrict_empty, add_zero, Q4]
  · rw [hνJ _ measurableSet_Ioc, Ioc_inter_Ioc_eq_empty_of_le' le_rfl,
      Ioc_inter_Ioc_eq_empty_of_le' (by linarith), Measure.restrict_empty, Measure.restrict_empty,
      add_zero, Q5]

/-- **Thm 8.4.5 ⇒ `GerverData`**: with Romik's ODEs, the tails give all the properties of Gerver's
triple that Theorem 8.5.7 uses. -/
theorem GerverODE.gerverData (hO : GerverODE φ θ K Bc Dc) (hT : GerverTails φ θ K Bc Dc) :
    GerverData φ θ K (Bset φ K) (Dset φ K) :=
  hT.gerverData (hO.sigma_left hT) (hO.sigma_right hT)

end Sofa
