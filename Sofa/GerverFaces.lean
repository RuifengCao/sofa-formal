/-
# Sofa/GerverFaces.lean — Baek Thm 8.4.3: the tails of Gerver's niche are the bottom arcs of `B_K`, `D_K`

Baek's Theorem 8.4.3 identifies the two "tails" `B : [t₃, t₅] → ℝ²` and `D : [t₀, t₂] → ℝ²` of the
niche of Gerver's sofa (`t₀ = 0`, `t₂ = θ`, `t₃ = π/2 − θ`, `t₅ = π/2`) with the lower boundary arcs
of the convex bodies `B_K`, `D_K` of Def 8.1.4.  His proof has two parts:

1. the tails lie in `B_K` resp. `D_K` — because they lie in `K`, in `H̆^R_K` resp. `H̆^L_K`, on or
   above the floor, and outside the niche, so Lemma 8.1.6 applies
   (`IsInjectiveCap.mem_Bset_of_not_mem_niche`, `IsInjectiveCap.mem_Dset_of_not_mem_niche`);
2. a continuous curve `c(t)` in a convex body `C` with `c(t)` on the supporting line of `C` at the
   normal angle `α + t` is the vertex curve: `c(t) = v^±_C(α + t)` (Thm 2.1.3: faces converge to
   vertices); at the end where the tail meets the core, the vertex lies on a supporting line at a
   *different* angle, which forces the boundary arc between the two angles to be degenerate
   (`sigmaK_Ioc_eq_zero_of_vtxP_mem`, `sigmaK_Ico_eq_zero_of_vtxM_mem`).

The output (`IsCap.gerver_B_side`, `IsCap.gerver_D_side`) is Thm 8.4.3 (1)–(3): `B(t) = v^±_{B_K}(π + t)`,
`X_{B_K} = B(t₃) = x^R_K` with `σ_{B_K} = 0` on `(π + φ, π + t₃]`, and `h_K(t) + h_{B_K}(π + t) = 1` on
`[t₃, t₅]`; mirror statements for `D`.  These are exactly the fields `X_B`, `B_null`, `B_eq` (and
`Y_D`, `D_null`, `D_eq`) of `GerverData`.

STATUS: [PROOF-C-local] round 33 (2026-09-23, Opus 5.5).
-/
import Sofa.QMax

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace Interval

namespace Sofa

variable {C K : Set ℝ²} {φ θ : ℝ}

/-! ## Degenerate boundary arcs -/

/-- If `v⁺_C(b)` lies on the supporting line of `C` at the angle `a` (`a < b < a + π`), the boundary
of `C` between the two normal angles is a single point: `σ_C((a, b]) = 0` and `v⁺_C(b) = v⁺_C(a)`. -/
theorem sigmaK_Ioc_eq_zero_of_vtxP_mem (hC : IsCompact C) (hne : C.Nonempty) {a b : ℝ}
    (hab : a < b) (hba : b < a + π) (h : ⟪vtxP C b, u a⟫ = supportFn C a) :
    sigmaK C (Ioc a b) = 0 ∧ vtxP C b = vtxP C a := by
  have hI := inner_vtxP_sub_eq_setIntegral hC hne (u a) hab.le
  rw [inner_sub_left, h, inner_vtxP_u, sub_self] at hI
  have hneg : ∀ t ∈ Ioc a b, ⟪v t, u a⟫ < 0 := fun t ht => by
    rw [inner_v_u_eq_sin]
    have := sin_pos_of_pos_of_lt_pi (x := t - a) (by linarith [ht.1]) (by linarith [ht.2])
    rw [show a - t = -(t - a) by ring, sin_neg]
    linarith
  have hint : IntegrableOn (fun t => -⟪v t, u a⟫) (Ioc a b) (sigmaK C) :=
    ((continuous_v.inner continuous_const).neg.continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[(sigmaK C).restrict (Ioc a b)] fun t => -⟪v t, u a⟫ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    show (0:ℝ) ≤ -⟪v t, u a⟫
    linarith [hneg t ht]
  have h0 : ¬ 0 < ∫ t in Ioc a b, -⟪v t, u a⟫ ∂(sigmaK C) := by
    rw [integral_neg, ← hI, neg_zero]; exact lt_irrefl 0
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint] at h0
  have hsupp : Function.support (fun t => -⟪v t, u a⟫) ∩ Ioc a b = Ioc a b := by
    refine inter_eq_right.2 fun t ht => ?_
    simp only [Function.mem_support, ne_eq, neg_eq_zero]
    exact (hneg t ht).ne
  rw [hsupp, not_lt, nonpos_iff_eq_zero] at h0
  refine ⟨h0, ?_⟩
  have hv := vtxP_sub_eq_setIntegral hC hne hab.le
  rw [setIntegral_measure_zero _ h0, sub_eq_zero] at hv
  exact hv

/-- `∫_{(a,b]} f dμ = μ({b}) f(b)` when `μ((a,b)) = 0` (vector-valued version). -/
lemma setIntegral_Ioc_of_null' {μ : Measure ℝ} {f : ℝ → ℝ²} {a b : ℝ} (hab : a < b)
    (hint : IntegrableOn f (Ioc a b) μ) (h0 : μ (Ioo a b) = 0) :
    ∫ t in Ioc a b, f t ∂μ = μ.real {b} • f b := by
  rw [← Ioo_union_right hab, setIntegral_union
    (Set.disjoint_singleton_right.2 fun h => lt_irrefl _ h.2) (measurableSet_singleton b)
    (hint.mono_set Ioo_subset_Ioc_self)
    (hint.mono_set (singleton_subset_iff.2 ⟨hab, le_rfl⟩)),
    setIntegral_measure_zero _ h0, integral_singleton, zero_add]

/-- If `v⁻_C(a)` lies on the supporting line of `C` at the angle `b` (`a < b < a + π`), then
`σ_C([a, b)) = 0` and `v⁻_C(b) = v⁻_C(a)`. -/
theorem sigmaK_Ico_eq_zero_of_vtxM_mem (hC : IsCompact C) (hne : C.Nonempty) {a b : ℝ}
    (hab : a < b) (hba : b < a + π) (h : ⟪vtxM C a, u b⟫ = supportFn C b) :
    sigmaK C (Ico a b) = 0 ∧ vtxM C b = vtxM C a := by
  have hM : ∀ t, vtxM C t = vtxP C t - edgeLength C t • v t := fun t => by
    rw [← vtxP_sub_vtxM]; abel
  have hℓ : ∀ t, (sigmaK C).real {t} = edgeLength C t := fun t => by
    rw [measureReal_def, sigmaK_singleton hC hne, ENNReal.toReal_ofReal (edgeLength_nonneg hC hne t)]
  have hI := inner_vtxP_sub_eq_setIntegral hC hne (u b) hab.le
  -- split `(a, b] = (a, b) ∪ {b}`; the integrand `sin (b − t)` vanishes at `b`
  have hint : IntegrableOn (fun t => ⟪v t, u b⟫) (Ioc a b) (sigmaK C) :=
    ((continuous_v.inner continuous_const).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  rw [← Ioo_union_right hab, setIntegral_union
    (Set.disjoint_singleton_right.2 fun h => lt_irrefl _ h.2) (measurableSet_singleton b)
    (hint.mono_set Ioo_subset_Ioc_self)
    (hint.mono_set (singleton_subset_iff.2 ⟨hab, le_rfl⟩)), integral_singleton,
    inner_v_u_eq_sin, sub_self, sin_zero, smul_zero, add_zero] at hI
  -- `⟪v⁻(b) − v⁻(a), u_b⟫ = 0`
  have hzero : ⟪vtxP C b - vtxP C a, u b⟫ + edgeLength C a * sin (b - a) = 0 := by
    have e1 : ⟪vtxM C b - vtxM C a, u b⟫ = 0 := by rw [inner_sub_left, inner_vtxM_u, h, sub_self]
    rw [hM b, hM a] at e1
    rw [← e1]
    simp only [inner_sub_left, real_inner_smul_left, inner_v_u_eq_sin, sub_self, sin_zero,
      mul_zero]
    ring
  have hpos : ∀ t ∈ Ioo a b, 0 < ⟪v t, u b⟫ := fun t ht => by
    rw [inner_v_u_eq_sin]
    exact sin_pos_of_pos_of_lt_pi (by linarith [ht.2]) (by linarith [ht.1])
  have hsab : 0 < sin (b - a) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hint' : IntegrableOn (fun t => ⟪v t, u b⟫) (Ioo a b) (sigmaK C) :=
    hint.mono_set Ioo_subset_Ioc_self
  have hnn : 0 ≤ᵐ[(sigmaK C).restrict (Ioo a b)] fun t => ⟪v t, u b⟫ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    show (0:ℝ) ≤ ⟪v t, u b⟫
    exact (hpos t ht).le
  have hIpos : 0 ≤ ∫ t in Ioo a b, ⟪v t, u b⟫ ∂(sigmaK C) := setIntegral_nonneg measurableSet_Ioo
    fun t ht => (hpos t ht).le
  have hla := edgeLength_nonneg hC hne a
  have hIz : ∫ t in Ioo a b, ⟪v t, u b⟫ ∂(sigmaK C) = 0 := by
    have : 0 ≤ edgeLength C a * sin (b - a) := mul_nonneg hla hsab.le
    linarith
  have hla0 : edgeLength C a = 0 := by
    have h1 : edgeLength C a * sin (b - a) = 0 := by linarith
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact h2
    · exact absurd h2 hsab.ne'
  -- `σ_C((a, b)) = 0`
  have hoo : sigmaK C (Ioo a b) = 0 := by
    have h0 : ¬ 0 < ∫ t in Ioo a b, ⟪v t, u b⟫ ∂(sigmaK C) := by rw [hIz]; exact lt_irrefl 0
    rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint'] at h0
    have hsupp : Function.support (fun t => ⟪v t, u b⟫) ∩ Ioo a b = Ioo a b := by
      refine inter_eq_right.2 fun t ht => ?_
      simp only [Function.mem_support, ne_eq]
      exact (hpos t ht).ne'
    rwa [hsupp, not_lt, nonpos_iff_eq_zero] at h0
  have hsa : sigmaK C {a} = 0 := by
    rw [sigmaK_singleton hC hne, hla0, ENNReal.ofReal_zero]
  refine ⟨?_, ?_⟩
  · rw [← Ioo_insert_left hab, insert_eq]
    exact measure_union_null hsa hoo
  · have hv := vtxP_sub_eq_setIntegral hC hne hab.le
    rw [setIntegral_Ioc_of_null' hab
      ((continuous_v.continuousOn.integrableOn_compact isCompact_Icc).mono_set
        Ioc_subset_Icc_self) hoo, hℓ] at hv
    rw [hM b, hM a, hla0, zero_smul, sub_zero]
    rw [sub_eq_iff_eq_add] at hv
    rw [hv]; abel

/-! ## A continuous curve along the faces is the vertex curve (Thm 2.1.3) -/

lemma tendsto_sub_const_nhdsGT (c t : ℝ) :
    Tendsto (fun s : ℝ => s - c) (𝓝[>] (c + t)) (𝓝[>] t) := by
  have h1 : Tendsto (fun s : ℝ => s - c) (𝓝 (c + t)) (𝓝 t) := by
    have := (continuous_sub_right c).tendsto (c + t); simpa using this
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (h1.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [mem_Ioi] at hs ⊢; linarith

lemma tendsto_sub_const_nhdsLT (c t : ℝ) :
    Tendsto (fun s : ℝ => s - c) (𝓝[<] (c + t)) (𝓝[<] t) := by
  have h1 : Tendsto (fun s : ℝ => s - c) (𝓝 (c + t)) (𝓝 t) := by
    have := (continuous_sub_right c).tendsto (c + t); simpa using this
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (h1.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [mem_Iio] at hs ⊢; linarith

/-- **Thm 2.1.3, applied to a curve**: if `c` is continuous on `[p, q]` and `c(t)` lies on the face
`e_C(α + t)` for every `t ∈ [p, q]`, then `c(t) = v⁺_C(α + t)` for `t ∈ [p, q)` and
`c(t) = v⁻_C(α + t)` for `t ∈ (p, q]`. -/
theorem eq_vtx_of_mem_edge (hC : IsCompact C) (hne : C.Nonempty) {c : ℝ → ℝ²} {α p q : ℝ}
    (hcont : ContinuousOn c (Icc p q)) (hface : ∀ t ∈ Icc p q, c t ∈ edge C (α + t)) :
    (∀ t ∈ Ico p q, c t = vtxP C (α + t)) ∧ (∀ t ∈ Ioc p q, c t = vtxM C (α + t)) := by
  constructor
  · intro t ht
    have hc : Tendsto c (𝓝[>] t) (𝓝 (c t)) := by
      have h1 := (hcont t (Ico_subset_Icc_self ht)).mono
        (show Ioo t q ⊆ Icc p q from fun s hs => ⟨by linarith [ht.1, hs.1], hs.2.le⟩)
      rwa [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsGT ht.2] at h1
    have h2 : Tendsto (fun s => c (s - α)) (𝓝[>] (α + t)) (𝓝 (c t)) :=
      hc.comp (tendsto_sub_const_nhdsGT α t)
    have h3 : Tendsto (fun s => c (s - α)) (𝓝[>] (α + t)) (𝓝 (vtxP C (α + t))) := by
      refine tendsto_of_mem_edge_right hC hne (α + t) ?_
      filter_upwards [Ioo_mem_nhdsGT (show α + t < α + q by linarith [ht.2])] with s hs
      have := hface (s - α) ⟨by linarith [ht.1, hs.1], by linarith [hs.2]⟩
      rwa [show α + (s - α) = s by ring] at this
    exact tendsto_nhds_unique h2 h3
  · intro t ht
    have hc : Tendsto c (𝓝[<] t) (𝓝 (c t)) := by
      have h1 := (hcont t (Ioc_subset_Icc_self ht)).mono
        (show Ioo p t ⊆ Icc p q from fun s hs => ⟨hs.1.le, by linarith [ht.2, hs.2]⟩)
      rwa [ContinuousWithinAt, nhdsWithin_Ioo_eq_nhdsLT ht.1] at h1
    have h2 : Tendsto (fun s => c (s - α)) (𝓝[<] (α + t)) (𝓝 (c t)) :=
      hc.comp (tendsto_sub_const_nhdsLT α t)
    have h3 : Tendsto (fun s => c (s - α)) (𝓝[<] (α + t)) (𝓝 (vtxM C (α + t))) := by
      refine tendsto_of_mem_edge_left hC hne (α + t) ?_
      filter_upwards [Ioo_mem_nhdsLT (show α + p < α + t by linarith [ht.1])] with s hs
      have := hface (s - α) ⟨by linarith [hs.1], by linarith [ht.2, hs.2]⟩
      rwa [show α + (s - α) = s by ring] at this
    exact tendsto_nhds_unique h2 h3

/-! ## The tails lie in `B_K`, `D_K` (first paragraph of Baek's proof of Thm 8.4.3) -/

/-- A point of `K ∩ H̆^R_K` on or above the floor and outside the niche lies in `B_K`
(Lemma 8.1.6 (1)). -/
theorem IsInjectiveCap.mem_Bset_of_not_mem_niche (hK : IsInjectiveCap K) (hφ0 : 0 < φ)
    {p : ℝ²} (hpK : p ∈ K) (hpy : 0 ≤ p 1) (hpN : p ∉ niche K (π / 2))
    (hpR : supportFn K φ - 1 ≤ ⟪p, u φ⟫) : p ∈ Bset φ K := by
  refine mem_Bset.2 ⟨hpK, fun t ht => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  rcases eq_or_lt_of_le ht.1 with h1 | h1
  · subst h1; linarith
  rcases eq_or_lt_of_le ht.2 with h2 | h2
  · subst h2
    rw [hK.isCap.supportFn_pi_div_two, inner_u_pi_div_two] at hlt
    linarith
  · refine hpN (mem_niche_iff.2 ⟨⟨hpy, ?_⟩, t, ⟨by linarith, h2⟩,
      hK.mem_QminusS_right hφ0 h1 h2.le hpR hlt⟩)
    rw [inner_u_pi_div_two]; exact hpy

/-- A point of `K ∩ H̆^L_K` on or above the floor and outside the niche lies in `D_K`
(Lemma 8.1.6 (2)). -/
theorem IsInjectiveCap.mem_Dset_of_not_mem_niche (hK : IsInjectiveCap K) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) {p : ℝ²} (hpK : p ∈ K) (hpy : 0 ≤ p 1) (hpN : p ∉ niche K (π / 2))
    (hpL : supportFn K (π - φ) - 1 ≤ ⟪p, u (π - φ)⟫) : p ∈ Dset φ K := by
  refine mem_Dset.2 ⟨hpK, fun t ht => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  rcases eq_or_lt_of_le ht.2 with h2 | h2
  · subst h2
    rw [show π / 2 - φ + π / 2 = π - φ by ring] at hlt
    linarith
  rcases eq_or_lt_of_le ht.1 with h1 | h1
  · subst h1
    rw [zero_add, hK.isCap.supportFn_pi_div_two, inner_u_pi_div_two] at hlt
    linarith
  · refine hpN (mem_niche_iff.2 ⟨⟨hpy, ?_⟩, t, ⟨h1, by linarith⟩,
      hK.mem_QminusS_left hφ0 hφ1 h1.le h2 hpL hlt⟩)
    rw [inner_u_pi_div_two]; exact hpy

/-! ## Theorem 8.4.3 -/

/-- **Baek Theorem 8.4.3, the `B`-side.** Let `Bc` be continuous on `[t₃, t₅] = [π/2 − θ, π/2]`,
with values in `B_K`, on the inner walls `b_K(t)` (Thm 8.4.1 (3)), and with `Bc(t₃) = x^R_K`
(Thm 8.4.1 (2)).  Then (3) `h_K(t) + h_{B_K}(π + t) = 1` on `[t₃, t₅]`; (1)
`Bc(t) = v⁺_{B_K}(π + t)` on `[t₃, t₅)` and `= v⁻_{B_K}(π + t)` on `(t₃, t₅]`; (2)
`X_{B_K} = x^R_K`, and `σ_{B_K}` vanishes on `(π + φ, π + t₃]`. -/
theorem IsCap.gerver_B_side (hK : IsCap K (π / 2)) (hφ0 : 0 < φ) (hφθ : φ < θ)
    (hθ : θ < π / 4) {Bc : ℝ → ℝ²} (hcont : ContinuousOn Bc (Icc (π / 2 - θ) (π / 2)))
    (hmem : ∀ t ∈ Icc (π / 2 - θ) (π / 2), Bc t ∈ Bset φ K)
    (hwall : ∀ t ∈ Icc (π / 2 - θ) (π / 2), ⟪Bc t, u t⟫ = supportFn K t - 1)
    (hend : Bc (π / 2 - θ) = innerCorner K φ) :
    (∀ t ∈ Icc (π / 2 - θ) (π / 2), supportFn K t + supportFn (Bset φ K) (π + t) = 1) ∧
    (∀ t ∈ Ico (π / 2 - θ) (π / 2), Bc t = vtxP (Bset φ K) (π + t)) ∧
    (∀ t ∈ Ioc (π / 2 - θ) (π / 2), Bc t = vtxM (Bset φ K) (π + t)) ∧
    vtxP (Bset φ K) (π + φ) = innerCorner K φ ∧
    sigmaK (Bset φ K) (Ioc (π + φ) (3 * π / 2 - θ)) = 0 := by
  have hpi := pi_pos
  have hBc : IsCompact (Bset φ K) := isCompact_Bset hK.isCompact
  have hBne : (Bset φ K).Nonempty := hK.Bset_nonempty hφ0.le
  have huπ : ∀ (p : ℝ²) (t : ℝ), ⟪p, u (π + t)⟫ = -⟪p, u t⟫ := fun p t => by
    rw [add_comm, u_add_pi, inner_neg_right]
  -- (3)
  have heq : ∀ t ∈ Icc (π / 2 - θ) (π / 2), supportFn K t + supportFn (Bset φ K) (π + t) = 1 := by
    intro t ht
    have hle := hK.supportFn_add_Bset_le hφ0.le (t := t) ⟨by linarith [ht.1], ht.2⟩
    have hge := le_supportFn hBc (hmem t ht) (π + t)
    rw [huπ, hwall t ht] at hge
    linarith
  -- the curve runs along the faces `e_{B_K}(π + t)`
  have hface : ∀ t ∈ Icc (π / 2 - θ) (π / 2), Bc t ∈ edge (Bset φ K) (π + t) := by
    intro t ht
    refine mem_edge_iff.2 ⟨hmem t ht, ?_⟩
    rw [huπ, hwall t ht]
    linarith [heq t ht]
  obtain ⟨hP, hM⟩ := eq_vtx_of_mem_edge hBc hBne hcont hface
  -- (2): the start `B(t₃) = x^R_K` lies on the supporting line at `π + φ`
  have hphi : supportFn (Bset φ K) (π + φ) = 1 - supportFn K φ := by
    have hle := hK.supportFn_add_Bset_le hφ0.le (t := φ) ⟨le_rfl, by linarith⟩
    have hge := le_supportFn hBc (hmem _ ⟨le_rfl, by linarith⟩) (π + φ)
    rw [huπ, hend, inner_innerCorner_u] at hge
    linarith
  have h3 : vtxP (Bset φ K) (π + (π / 2 - θ)) = innerCorner K φ := by
    rw [← hend, hP _ ⟨le_rfl, by linarith⟩]
  have hon : ⟪vtxP (Bset φ K) (3 * π / 2 - θ), u (π + φ)⟫ = supportFn (Bset φ K) (π + φ) := by
    rw [show 3 * π / 2 - θ = π + (π / 2 - θ) by ring, h3, huπ, inner_innerCorner_u, hphi]
    ring
  obtain ⟨hnull, hv⟩ := sigmaK_Ioc_eq_zero_of_vtxP_mem hBc hBne (a := π + φ)
    (b := 3 * π / 2 - θ) (by linarith) (by linarith) hon
  refine ⟨heq, hP, hM, ?_, hnull⟩
  rw [← hv, show 3 * π / 2 - θ = π + (π / 2 - θ) by ring, h3]

/-- **Baek Theorem 8.4.3, the `D`-side.** Let `Dc` be continuous on `[t₀, t₂] = [0, θ]`, with values
in `D_K`, on the inner walls `d_K(t)` (Thm 8.4.1 (3)), and with `Dc(t₂) = x^L_K` (Thm 8.4.1 (2)).
Then (3) `h_K(π/2 + t) + h_{D_K}(3π/2 + t) = 1` on `[0, θ]`; (1) `Dc(t) = v^±_{D_K}(3π/2 + t)`;
(2) `Y_{D_K} = x^L_K`, and `σ_{D_K}` vanishes on `[3π/2 + t₂, 2π − φ)`. -/
theorem IsCap.gerver_D_side (hK : IsCap K (π / 2)) (hφ0 : 0 < φ) (hφθ : φ < θ)
    (hθ : θ < π / 4) {Dc : ℝ → ℝ²} (hcont : ContinuousOn Dc (Icc 0 θ))
    (hmem : ∀ t ∈ Icc 0 θ, Dc t ∈ Dset φ K)
    (hwall : ∀ t ∈ Icc 0 θ, ⟪Dc t, u (t + π / 2)⟫ = supportFn K (t + π / 2) - 1)
    (hend : Dc θ = innerCorner K (π / 2 - φ)) :
    (∀ t ∈ Icc 0 θ, supportFn K (π / 2 + t) + supportFn (Dset φ K) (3 * π / 2 + t) = 1) ∧
    (∀ t ∈ Ico 0 θ, Dc t = vtxP (Dset φ K) (3 * π / 2 + t)) ∧
    (∀ t ∈ Ioc 0 θ, Dc t = vtxM (Dset φ K) (3 * π / 2 + t)) ∧
    vtxM (Dset φ K) (2 * π - φ) = innerCorner K (π / 2 - φ) ∧
    sigmaK (Dset φ K) (Ico (3 * π / 2 + θ) (2 * π - φ)) = 0 := by
  have hpi := pi_pos
  have hDc : IsCompact (Dset φ K) := isCompact_Dset hK.isCompact
  have hDne : (Dset φ K).Nonempty := hK.Dset_nonempty hφ0.le
  have hu32 : ∀ (p : ℝ²) (t : ℝ), ⟪p, u (3 * π / 2 + t)⟫ = -⟪p, u (t + π / 2)⟫ := fun p t => by
    rw [show 3 * π / 2 + t = t + π / 2 + π by ring, u_add_pi, inner_neg_right]
  -- (3)
  have heq : ∀ t ∈ Icc 0 θ, supportFn K (π / 2 + t) + supportFn (Dset φ K) (3 * π / 2 + t) = 1 := by
    intro t ht
    have hle := hK.supportFn_add_Dset_le hφ0.le (t := t) ⟨ht.1, by linarith [ht.2]⟩
    have hge := le_supportFn hDc (hmem t ht) (3 * π / 2 + t)
    rw [hu32, hwall t ht] at hge
    rw [show π / 2 + t = t + π / 2 by ring] at hle ⊢
    linarith
  have hface : ∀ t ∈ Icc 0 θ, Dc t ∈ edge (Dset φ K) (3 * π / 2 + t) := by
    intro t ht
    refine mem_edge_iff.2 ⟨hmem t ht, ?_⟩
    rw [hu32, hwall t ht]
    have := heq t ht
    rw [show π / 2 + t = t + π / 2 by ring] at this
    linarith
  obtain ⟨hP, hM⟩ := eq_vtx_of_mem_edge hDc hDne hcont hface
  -- (2): the end `D(t₂) = x^L_K` lies on the supporting line at `2π − φ = 3π/2 + φ^L`
  have hphi : supportFn (Dset φ K) (2 * π - φ) = 1 - supportFn K (π - φ) := by
    have hle := hK.supportFn_add_Dset_le hφ0.le (t := π / 2 - φ) ⟨by linarith, le_rfl⟩
    rw [show π / 2 + (π / 2 - φ) = π - φ by ring,
      show 3 * π / 2 + (π / 2 - φ) = 2 * π - φ by ring] at hle
    have hge := le_supportFn hDc (hmem θ ⟨by linarith, le_rfl⟩) (2 * π - φ)
    rw [show 2 * π - φ = 3 * π / 2 + (π / 2 - φ) by ring, hu32, hend,
      inner_innerCorner_u_add, show π / 2 - φ + π / 2 = π - φ by ring] at hge
    rw [show 3 * π / 2 + (π / 2 - φ) = 2 * π - φ by ring] at hge
    linarith
  have h2 : vtxM (Dset φ K) (3 * π / 2 + θ) = innerCorner K (π / 2 - φ) := by
    rw [← hend, hM _ ⟨by linarith, le_rfl⟩]
  have hon : ⟪vtxM (Dset φ K) (3 * π / 2 + θ), u (2 * π - φ)⟫
      = supportFn (Dset φ K) (2 * π - φ) := by
    rw [h2, show 2 * π - φ = 3 * π / 2 + (π / 2 - φ) by ring, hu32, inner_innerCorner_u_add,
      show π / 2 - φ + π / 2 = π - φ by ring, show 3 * π / 2 + (π / 2 - φ) = 2 * π - φ by ring,
      hphi]
    ring
  obtain ⟨hnull, hv⟩ := sigmaK_Ico_eq_zero_of_vtxM_mem hDc hDne (a := 3 * π / 2 + θ)
    (b := 2 * π - φ) (by linarith) (by linarith) hon
  exact ⟨heq, hP, hM, by rw [hv, h2], hnull⟩

/-! ## Thm 8.4.1 (2)–(4) for the tails, and the derivation of `GerverData` -/

/-- **Gerver's angles** (Def 8.4.1): `0 < φ ≤ 1/25` and `φ < θ < π/4`.  For Gerver's constants
these are proved from Romik's system `ABφθSpec` by a verified computation
(`Sofa.GC.gerver_angles`, `Sofa/GerverConst.lean`). -/
structure GerverAngles (φ θ : ℝ) : Prop where
  phi_pos : 0 < φ
  phi_le : φ ≤ 1 / 25
  phi_lt_theta : φ < θ
  theta_lt : θ < π / 4

/-- **Baek Theorem 8.4.1 (2)–(4)**, the part about the two tails `B : [t₃, t₅] → ℝ²`,
`D : [t₀, t₂] → ℝ²` of the niche of `K = C(G)` (`t₀ = 0`, `t₂ = θ`, `t₃ = π/2 − θ`, `t₅ = π/2`),
together with the facts about `K` that Chapter 8 needs (Thm 6.1.2: `K` is injective; `K` is the
cap of a monotone sofa, so `N(K) ⊆ K` by Thm 2.5.9; `|K| ≥ |G| ≥ 2.2`), and the bounds on
Gerver's angles (`GerverAngles`, proved in `Sofa/GerverConst.lean`).  Baek does not prove
Thm 8.4.1 (Rem 8.4.1).  Formalized statements:

* (2) the tails bound the niche: their interior points are limits of points of `N(K)` but not in
  `N(K)`, and the boundary curve closes up with the core, `B(t₃) = x(t₁) = x^R_K`,
  `D(t₂) = x(t₄) = x^L_K`;
* (3) `B(t) ∈ b_K(t)`, `D(t) ∈ d_K(t)` (only the full lines are used);
* (4) `B'(t) = β(t) v_t` with `β < 0` and `D'(t) = δ(t) u_t` with `δ > 0` (as right derivatives:
  the curves are only piecewise smooth). -/
structure GerverTails (φ θ : ℝ) (K : Set ℝ²) (Bc Dc : ℝ → ℝ²) : Prop
    extends GerverAngles φ θ where
  injective : IsInjectiveCap K
  niche_subset : niche K (π / 2) ⊆ K
  area : 11 / 5 ≤ volume.real K
  B_closure : ∀ t ∈ Ioo (π / 2 - θ) (π / 2), Bc t ∈ closure (niche K (π / 2))
  B_not_mem : ∀ t ∈ Ioo (π / 2 - θ) (π / 2), Bc t ∉ niche K (π / 2)
  D_closure : ∀ t ∈ Ioo 0 θ, Dc t ∈ closure (niche K (π / 2))
  D_not_mem : ∀ t ∈ Ioo 0 θ, Dc t ∉ niche K (π / 2)
  B_start : Bc (π / 2 - θ) = innerCorner K φ
  D_end : Dc θ = innerCorner K (π / 2 - φ)
  B_wall : ∀ t ∈ Icc (π / 2 - θ) (π / 2), ⟪Bc t, u t⟫ = supportFn K t - 1
  D_wall : ∀ t ∈ Icc 0 θ, ⟪Dc t, u (t + π / 2)⟫ = supportFn K (t + π / 2) - 1
  B_cont : ContinuousOn Bc (Icc (π / 2 - θ) (π / 2))
  D_cont : ContinuousOn Dc (Icc 0 θ)
  B_deriv : ∃ β : ℝ → ℝ, ∀ t ∈ Ico (π / 2 - θ) (π / 2),
    β t < 0 ∧ HasDerivWithinAt Bc (β t • v t) (Ici t) t
  D_deriv : ∃ δ : ℝ → ℝ, ∀ t ∈ Ico 0 θ, 0 < δ t ∧ HasDerivWithinAt Dc (δ t • u t) (Ici t) t

variable {Bc Dc : ℝ → ℝ²}

lemma closure_niche_subset (hK : IsCap K (π / 2)) (hN : niche K (π / 2) ⊆ K) :
    closure (niche K (π / 2)) ⊆ K :=
  closure_minimal hN hK.isCompact.isClosed

lemma closure_niche_subset_floor (K : Set ℝ²) :
    closure (niche K (π / 2)) ⊆ {p : ℝ² | 0 ≤ p 1} := by
  refine closure_minimal (fun p hp => (mem_niche_iff.1 hp).1.1) ?_
  exact isClosed_le continuous_const (EuclideanSpace.proj (1 : Fin 2)).continuous

/-- A continuous curve on `[a, b]` whose values on `(a, b)` lie in a closed set `F` has all its
values in `F`. -/
lemma mem_of_mem_Ioo {c : ℝ → ℝ²} {a b : ℝ} (hab : a < b) (hc : ContinuousOn c (Icc a b))
    {F : Set ℝ²} (hF : IsClosed F) (h : ∀ t ∈ Ioo a b, c t ∈ F) : ∀ t ∈ Icc a b, c t ∈ F := by
  intro t ht
  have hcl : t ∈ closure (Ioo a b) := by rw [closure_Ioo hab.ne]; exact ht
  have h1 := ((hc t ht).mono Ioo_subset_Icc_self).mem_closure_image hcl
  exact closure_minimal (image_subset_iff.2 h) hF h1

/-- The tail `B` lies in `B_K` (first paragraph of Baek's proof of Thm 8.4.3). -/
theorem GerverTails.B_mem (hG : GerverTails φ θ K Bc Dc) :
    ∀ t ∈ Icc (π / 2 - θ) (π / 2), Bc t ∈ Bset φ K := by
  have hpi := pi_pos
  have hφ0 := hG.phi_pos
  have hφθ := hG.phi_lt_theta
  have hθ := hG.theta_lt
  have hK := hG.injective
  obtain ⟨β, hβ⟩ := hG.B_deriv
  -- `⟪B(t), u_φ⟫` is nondecreasing: `B' = β v_t`, `⟪v_t, u_φ⟫ = sin (φ − t) < 0`
  have hmono : MonotoneOn (fun t => ⟪Bc t, u φ⟫) (Icc (π / 2 - θ) (π / 2)) := by
    refine monotoneOn_Icc_of_rightDeriv_nonneg (F' := fun t => ⟪β t • v t, u φ⟫)
      (hG.B_cont.inner continuousOn_const) (fun t ht => ?_) (fun t ht => ?_)
    · have h1 := ((hβ t ⟨ht.1.le, ht.2⟩).2.mono Ioi_subset_Ici_self).inner (𝕜 := ℝ)
        (hasDerivWithinAt_const t (Ioi t) (u φ))
      rw [inner_zero_right, zero_add] at h1
      exact h1
    · show 0 ≤ ⟪β t • v t, u φ⟫
      rw [real_inner_smul_left, inner_v_u_eq_sin]
      have hs : sin (φ - t) < 0 := by
        rw [show φ - t = -(t - φ) by ring, sin_neg]
        linarith [sin_pos_of_pos_of_lt_pi (x := t - φ) (by linarith [ht.1]) (by linarith [ht.2])]
      exact mul_nonneg_of_nonpos_of_nonpos (hβ t ⟨ht.1.le, ht.2⟩).1.le hs.le
  have hin : ∀ t ∈ Ioo (π / 2 - θ) (π / 2), Bc t ∈ Bset φ K := by
    intro t ht
    have hpK := closure_niche_subset hK.isCap hG.niche_subset (hG.B_closure t ht)
    have hpy := closure_niche_subset_floor K (hG.B_closure t ht)
    refine hK.mem_Bset_of_not_mem_niche hφ0 hpK hpy (hG.B_not_mem t ht) ?_
    have := hmono ⟨le_rfl, by linarith⟩ ⟨ht.1.le, ht.2.le⟩ ht.1.le
    simp only [hG.B_start, inner_innerCorner_u] at this
    exact this
  exact mem_of_mem_Ioo (by linarith) hG.B_cont (isCompact_Bset hK.isCap.isCompact).isClosed hin

/-- The tail `D` lies in `D_K`. -/
theorem GerverTails.D_mem (hG : GerverTails φ θ K Bc Dc) :
    ∀ t ∈ Icc 0 θ, Dc t ∈ Dset φ K := by
  have hpi := pi_pos
  have hφ0 := hG.phi_pos
  have hφθ := hG.phi_lt_theta
  have hθ := hG.theta_lt
  have hK := hG.injective
  obtain ⟨δ, hδ⟩ := hG.D_deriv
  -- `⟪D(t), u_{π−φ}⟫` is nonincreasing: `⟪u_t, u_{π−φ}⟫ = cos (t − (π − φ)) < 0`
  have hanti : AntitoneOn (fun t => ⟪Dc t, u (π - φ)⟫) (Icc 0 θ) := by
    refine antitoneOn_Icc_of_rightDeriv_nonpos (F' := fun t => ⟪δ t • u t, u (π - φ)⟫)
      (hG.D_cont.inner continuousOn_const) (fun t ht => ?_) (fun t ht => ?_)
    · have h1 := ((hδ t ⟨ht.1.le, ht.2⟩).2.mono Ioi_subset_Ici_self).inner (𝕜 := ℝ)
        (hasDerivWithinAt_const t (Ioi t) (u (π - φ)))
      rw [inner_zero_right, zero_add] at h1
      exact h1
    · show ⟪δ t • u t, u (π - φ)⟫ ≤ 0
      rw [real_inner_smul_left, inner_u_u_eq_cos]
      have hc : cos (t - (π - φ)) < 0 := by
        rw [show t - (π - φ) = -(π - φ - t) by ring, cos_neg]
        exact cos_neg_of_pi_div_two_lt_of_lt (by linarith [ht.2]) (by linarith [ht.1])
      exact mul_nonpos_of_nonneg_of_nonpos (hδ t ⟨ht.1.le, ht.2⟩).1.le hc.le
  have hin : ∀ t ∈ Ioo 0 θ, Dc t ∈ Dset φ K := by
    intro t ht
    have hpK := closure_niche_subset hK.isCap hG.niche_subset (hG.D_closure t ht)
    have hpy := closure_niche_subset_floor K (hG.D_closure t ht)
    refine hK.mem_Dset_of_not_mem_niche hφ0 (by linarith) hpK hpy (hG.D_not_mem t ht) ?_
    have := hanti ⟨ht.1.le, ht.2.le⟩ ⟨by linarith, le_rfl⟩ ht.2.le
    simp only [hG.D_end] at this
    have e := inner_innerCorner_u_add K (π / 2 - φ)
    rw [show π / 2 - φ + π / 2 = π - φ by ring] at e
    rw [e] at this
    exact this
  exact mem_of_mem_Ioo (by linarith) hG.D_cont (isCompact_Dset hK.isCap.isCompact).isClosed hin

lemma iotaV_eq (K : Set ℝ²) (t : ℝ) : iotaV K t = armGp K t - 1 := by
  rw [iotaV, armGp_eq_add]; ring

lemma iotaU_eq (K : Set ℝ²) (t : ℝ) : iotaU K t = armFp K t - 1 := by
  rw [iotaU, armFp_eq]; ring

/-- **Baek Thm 8.4.3 ⇒ `GerverData`**: the tails, with the measure identities of Thm 8.4.5, give
all the properties of Gerver's triple that Theorem 8.5.7 uses. -/
theorem GerverTails.gerverData (hG : GerverTails φ θ K Bc Dc)
    (hleft : (sigmaK K).restrict (Ico 0 (π / 2))
      = (iotaK K).restrict (Ico φ (π / 2 - φ))
        + (sigmaBreve (Bset φ K)).restrict (Ico (π / 2 - θ) (π / 2)))
    (hright : (sigmaK K).restrict (Ioc (π / 2) π)
      = (iotaK K).restrict (Ioc (π / 2 + φ) (π - φ))
        + (sigmaBreve (Dset φ K)).restrict (Ioc (π / 2) (π / 2 + θ))) :
    GerverData φ θ K (Bset φ K) (Dset φ K) := by
  have hpi := pi_pos
  have hφ0 := hG.phi_pos
  have hφθ := hG.phi_lt_theta
  have hθ := hG.theta_lt
  have hK := hG.injective
  have hcap := hK.isCap
  obtain ⟨hBeq, -, -, hXB, hBnull⟩ := hcap.gerver_B_side hφ0 hφθ hθ hG.B_cont hG.B_mem
    hG.B_wall hG.B_start
  obtain ⟨hDeq, -, -, hYD, hDnull⟩ := hcap.gerver_D_side hφ0 hφθ hθ hG.D_cont hG.D_mem
    hG.D_wall hG.D_end
  have hL := hK.inL hG.area hφ0 hG.phi_le hG.niche_subset
  exact
    { phi_pos := hφ0
      phi_lt_theta := hφθ
      theta_lt := hθ
      cap := hcap
      interior_nonempty := hL.interior_nonempty
      B_compact := hL.B_compact
      B_nonempty := hL.B_nonempty
      D_compact := hL.D_compact
      D_nonempty := hL.D_nonempty
      leq := hL.eq
      X_B := hXB
      Y_D := hYD
      B_null := measure_mono_null Ioo_subset_Ioc_self hBnull
      D_null := measure_mono_null Ioo_subset_Ico_self hDnull
      B_eq := hBeq
      D_eq := hDeq
      sigma_left := hleft
      sigma_right := hright
      iotaV_nonneg := fun t ht => by
        rw [iotaV_eq]
        linarith [(hK.one_lt_arm t ⟨by linarith [ht.1], by linarith [ht.2]⟩).2]
      iotaU_nonneg := fun t ht => by
        rw [iotaU_eq]
        linarith [(hK.one_lt_arm t ⟨by linarith [ht.1], by linarith [ht.2]⟩).1] }

end Sofa
