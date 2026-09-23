/-
# Sofa/Translate.lean — Theorem 7.1.3 for an arbitrary convex body

`Sofa/WedgeCover.lean` proves `|K| = ½ ∫_{(t₀,t₀+2π]} h_K dσ_K` under `AreaSetup K hm R`, which
forces the origin to be an *interior* point of `K`.  Baek applies the theorem to **caps**, where
the origin sits on the boundary.  Both sides are translation-covariant, so one translation removes
the restriction:

* `arcFn (K + c) t = arcFn K t + c₁` — a *constant* shift, because
  `⟪c, v_t⟫ + ∫_0^t ⟪c, u_s⟫ ds = c₁` identically.  Hence `σ_{K+c} = σ_K`.
* `∫_{(a,b]} ⟪c, u_r⟫ dσ_K(r) = ⟪v⁺_K(b) − v⁺_K(a), R_{π/2} c⟫`, which vanishes over a full turn
  by `vtxP_add_two_pi`.  Hence `curveG (K + c) = curveG K` over a full turn.

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.WedgeCover

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²}

/-! ## The basic objects under translation -/

lemma edge_tr (hK : IsCompact K) (hne : K.Nonempty) (c : ℝ²) (t : ℝ) :
    edge (tr c K) t = tr c (edge K t) := by
  have hsup : supportFn (tr c K) t = supportFn K t + ⟪c, u t⟫ := supportFn_tr hK hne c t
  ext q
  rw [mem_tr]
  constructor
  · rintro ⟨hq1, hq2⟩
    refine ⟨mem_tr.1 hq1, ?_⟩
    have h2 : ⟪q, u t⟫ = supportFn (tr c K) t := hq2
    rw [hsup] at h2
    show ⟪q - c, u t⟫ = supportFn K t
    rw [inner_sub_left, h2]; ring
  · rintro ⟨hq1, hq2⟩
    refine ⟨mem_tr.2 hq1, ?_⟩
    have h2 : ⟪q - c, u t⟫ = supportFn K t := hq2
    rw [inner_sub_left] at h2
    show ⟪q, u t⟫ = supportFn (tr c K) t
    rw [hsup]; linarith

lemma edgeMax_tr (hK : IsCompact K) (hne : K.Nonempty) (c : ℝ²) (t : ℝ) :
    edgeMax (tr c K) t = edgeMax K t + ⟪c, v t⟫ := by
  rw [edgeMax, edgeMax, edge_tr hK hne c t,
    supportFn_tr (isCompact_edge hK t) (edge_nonempty hK hne t) c (t + π / 2),
    u_add_pi_div_two]

lemma vtxP_tr (hK : IsCompact K) (hne : K.Nonempty) (c : ℝ²) (t : ℝ) :
    vtxP (tr c K) t = vtxP K t + c := by
  have hc : ⟪c, u t⟫ • u t + ⟪c, v t⟫ • v t = c := (decomp_u_v t c).symm
  have key : supportFn K t • u t + ⟪c, u t⟫ • u t + (edgeMax K t • v t + ⟪c, v t⟫ • v t)
      = supportFn K t • u t + edgeMax K t • v t + (⟪c, u t⟫ • u t + ⟪c, v t⟫ • v t) := by
    module
  rw [vtxP, vtxP, supportFn_tr hK hne c t, edgeMax_tr hK hne c t, add_smul, add_smul, key, hc]

/-- **The key cancellation**: `arcFn` shifts by a *constant* under translation, because
`∫_0^t ⟪c, u_s⟫ ds = ⟪c, v_0⟫ − ⟪c, v_t⟫` cancels the `⟪c, v_t⟫` coming from the vertex. -/
theorem arcFn_tr (hK : IsCompact K) (hne : K.Nonempty) (c : ℝ²) (t : ℝ) :
    arcFn (tr c K) t = arcFn K t + c 1 := by
  have hcont : Continuous fun s : ℝ => ⟪c, u s⟫ := continuous_const.inner continuous_u
  have hI : ∫ s in (0 : ℝ)..t, supportFn (tr c K) s
      = (∫ s in (0 : ℝ)..t, supportFn K s) + (⟪c, v 0⟫ - ⟪c, v t⟫) := by
    have hpt : ∀ s : ℝ, supportFn (tr c K) s = supportFn K s + ⟪c, u s⟫ :=
      fun s => supportFn_tr hK hne c s
    simp only [hpt]
    rw [intervalIntegral.integral_add (integrable_supportFn hK hne 0 t)
      (hcont.intervalIntegrable 0 t), integral_inner_u]
  have hv0 : ⟪c, v 0⟫ = c 1 := by
    rw [inner_eq, v_coord_zero, v_coord_one, Real.sin_zero, Real.cos_zero]; ring
  rw [arcFn, arcFn, vtxP_tr hK hne c t, hI, inner_add_left, hv0]
  ring

/-- Hence the surface area measure is translation-invariant. -/
theorem sigmaK_tr (hK : IsCompact K) (hne : K.Nonempty) (c : ℝ²) :
    sigmaK (tr c K) = sigmaK K := by
  refine Measure.ext_of_Ioc _ _ fun a b _ => ?_
  rw [sigmaK_Ioc (isCompact_tr hK c) (nonempty_tr hne c), sigmaK_Ioc hK hne,
    arcFn_tr hK hne c b, arcFn_tr hK hne c a]
  ring_nf

/-! ## The vanishing of `∫ ⟪c, u_t⟫ dσ_K` over a full turn -/

/-- The quarter turn `R_{π/2} c`, in coordinates. -/
def rotQ (c : ℝ²) : ℝ² := !₂[-(c 1), c 0]

lemma inner_u_eq_inner_v_rotQ (c : ℝ²) (t : ℝ) : ⟪c, u t⟫ = ⟪v t, rotQ c⟫ := by
  rw [inner_eq, inner_eq, u_coord_zero, u_coord_one, v_coord_zero, v_coord_one, rotQ,
    vec_coord_zero, vec_coord_one]
  ring

lemma integrableOn_inner_u_sigmaK (K : Set ℝ²) (c : ℝ²) (a b : ℝ) :
    IntegrableOn (fun t => ⟪c, u t⟫) (Ioc a b) (sigmaK K) :=
  (ContinuousOn.integrableOn_compact isCompact_Icc
    (continuous_const.inner continuous_u).continuousOn).mono_set Ioc_subset_Icc_self

theorem setIntegral_inner_u_sigmaK (hK : IsCompact K) (hne : K.Nonempty) (c : ℝ²) {a b : ℝ}
    (hab : a ≤ b) :
    ∫ t in Ioc a b, ⟪c, u t⟫ ∂(sigmaK K) = ⟪vtxP K b - vtxP K a, rotQ c⟫ := by
  rw [inner_vtxP_sub_eq_setIntegral hK hne (rotQ c) hab]
  simp only [inner_u_eq_inner_v_rotQ]

/-- Over a full turn the integral vanishes, because `v⁺_K` is `2π`-periodic. -/
theorem setIntegral_inner_u_sigmaK_full (hK : IsCompact K) (hne : K.Nonempty) (c : ℝ²) (t₀ : ℝ) :
    ∫ t in Ioc t₀ (t₀ + 2 * π), ⟪c, u t⟫ ∂(sigmaK K) = 0 := by
  rw [setIntegral_inner_u_sigmaK hK hne c (by linarith [pi_pos]), vtxP_add_two_pi, sub_self,
    inner_zero_left]

/-- **`curveG` is translation-invariant over a full turn.** -/
theorem curveG_tr (hK : IsCompact K) (hne : K.Nonempty) (c : ℝ²) (t₀ : ℝ) :
    curveG (tr c K) t₀ (t₀ + 2 * π) = curveG K t₀ (t₀ + 2 * π) := by
  rw [curveG, curveG, sigmaK_tr hK hne]
  have hpt : ∀ s : ℝ, supportFn (tr c K) s = supportFn K s + ⟪c, u s⟫ :=
    fun s => supportFn_tr hK hne c s
  have hsplit : ∫ t in Ioc t₀ (t₀ + 2 * π), supportFn (tr c K) t ∂(sigmaK K)
      = (∫ t in Ioc t₀ (t₀ + 2 * π), supportFn K t ∂(sigmaK K))
        + ∫ t in Ioc t₀ (t₀ + 2 * π), ⟪c, u t⟫ ∂(sigmaK K) := by
    simp only [hpt]
    exact integral_add (integrableOn_supportFn_sigmaK hK hne _ _)
      (integrableOn_inner_u_sigmaK K c _ _)
  rw [hsplit, setIntegral_inner_u_sigmaK_full hK hne c t₀, add_zero]

/-! ## Theorem 7.1.3 for an arbitrary convex body -/

theorem exists_areaSetup_of_mem_interior (hK : IsCompact K) (hconv : Convex ℝ K)
    {c : ℝ²} (hc : c ∈ interior K) : ∃ hm R : ℝ, AreaSetup (tr (-c) K) hm R := by
  obtain ⟨r, hr0, hball⟩ := Metric.isOpen_iff.1 isOpen_interior c hc
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ²)).1
    (isCompact_tr hK (-c)).isBounded
  have hKne : K.Nonempty := ⟨c, interior_subset hc⟩
  have hmem : ∀ p : ℝ², ‖p‖ < r → p ∈ tr (-c) K := by
    intro p hp
    have h1 : p + c ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_eq_norm]; simpa using hp
    have h2 : p + c ∈ K := interior_subset (hball h1)
    have : (p + c) + -c ∈ tr (-c) K := add_mem_tr h2
    simpa using this
  refine ⟨r / 2, R, ?_, ?_, ?_, ?_, by linarith, fun t => ?_, fun p hp => ?_⟩
  · exact isCompact_tr hK (-c)
  · exact nonempty_tr hKne (-c)
  · intro x hx y hy a b ha hb hab
    rw [mem_tr] at hx hy ⊢
    have hx' : x + c ∈ K := by simpa using hx
    have hy' : y + c ∈ K := by simpa using hy
    have hmem2 := hconv hx' hy' ha hb hab
    have hid : a • (x + c) + b • (y + c) = a • x + b • y - -c := by
      have hone : (a + b) • c = c := by rw [hab, one_smul]
      rw [sub_neg_eq_add,
        show a • (x + c) + b • (y + c) = a • x + b • y + (a + b) • c from by module, hone]
    rwa [hid] at hmem2
  · rw [mem_tr]; simpa using interior_subset hc
  · have hnorm : ‖(r / 2) • u t‖ < r := by
      rw [norm_smul, norm_u, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have h := le_supportFn (isCompact_tr hK (-c)) (hmem _ hnorm) t
    rwa [real_inner_smul_left, inner_u_u, mul_one] at h
  · exact mem_closedBall_zero_iff.1 (hR hp)

/-- **Theorem 7.1.3** for a convex body with an interior point `c` (no position assumption). -/
theorem volumeReal_eq_curveG_of_mem_interior (hK : IsCompact K) (hconv : Convex ℝ K)
    {c : ℝ²} (hc : c ∈ interior K) (t₀ : ℝ) :
    volume.real K = curveG K t₀ (t₀ + 2 * π) := by
  obtain ⟨hm, R, hset⟩ := exists_areaSetup_of_mem_interior hK hconv hc
  have h1 := volumeReal_eq_curveG hset t₀
  rw [curveG_tr hK ⟨c, interior_subset hc⟩ (-c) t₀] at h1
  rwa [measureReal_def, volume_tr, ← measureReal_def] at h1

/-- **Theorem 7.1.3**: `|K| = ½ ∫_{(t₀, t₀+2π]} h_K dσ_K` for every convex body with nonempty
interior. -/
theorem volumeReal_eq_curveG_of_interior_nonempty (hK : IsCompact K) (hconv : Convex ℝ K)
    (hint : (interior K).Nonempty) (t₀ : ℝ) :
    volume.real K = curveG K t₀ (t₀ + 2 * π) :=
  volumeReal_eq_curveG_of_mem_interior hK hconv hint.choose_spec t₀
