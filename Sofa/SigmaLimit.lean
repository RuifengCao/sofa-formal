/-
# Sofa/SigmaLimit.lean — weak convergence of `σ_K` under Hausdorff convergence

`σ_K` is the Lebesgue–Stieltjes measure of `arcFn K t = ⟪v⁺_K(t), v_t⟫ + ∫_0^t h_K`
(`Sofa/SurfaceArea.lean`), so `σ_{K_i} → σ_K` weakly as soon as `arcFn K_i → arcFn K` pointwise
at the continuity points of `arcFn K` — i.e. at every `t` with `σ_K({t}) = |e_K(t)| = 0`.

The support-function part converges uniformly (`tendsto_supportFn_uniformly`), so everything
reduces to

    `|e_K(t)| = 0` ⟹ `v⁺_{K_i}(t) → v⁺_K(t)`,

which is proved here by a direct `ε`–`η` argument: if `e_K(t)` is the single point `q` then
`⟪·, u_t⟫` is bounded away from `h_K(t)` on `K \ B(q, ε)`, and a set at Hausdorff distance `< η`
must have its whole `t`-edge inside `B(q, ε)` once `η` is small.

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.ArmLength
import Sofa.Hausdorff

noncomputable section

open Real Set Filter Topology MeasureTheory Metric
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²}

/-! ## Degenerate edges -/

/-- `e_K(t)` is a single point exactly when it has length zero. -/
theorem edge_eq_singleton (hK : IsCompact K) (hne : K.Nonempty) {t : ℝ}
    (hdeg : edgeLength K t = 0) : edge K t = {vtxP K t} := by
  apply Set.Subset.antisymm
  · intro p hp
    have h1 : ⟪p, u t⟫ = supportFn K t := hp.2
    have h2 : ⟪p, v t⟫ ≤ edgeMax K t := inner_v_le_edgeMax hK hp
    have h3 : edgeMin K t ≤ ⟪p, v t⟫ := edgeMin_le_inner_v hK hp
    have h4 : ⟪p, v t⟫ = edgeMax K t := by
      rw [edgeLength] at hdeg; linarith
    rw [Set.mem_singleton_iff, decomp_u_v t p, h1, h4, vtxP]
  · rw [Set.singleton_subset_iff]; exact vtxP_mem_edge hK hne t

/-- If `e_K(t)` is a single point, every compact set close enough to `K` in Hausdorff distance
has its whole `t`-edge inside `B(v⁺_K(t), ε)`. -/
theorem exists_hausdorffDist_edge_subset_ball (hK : IsCompact K) (hne : K.Nonempty) {t : ℝ}
    (hdeg : edgeLength K t = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > 0, ∀ K' : Set ℝ², IsCompact K' → K'.Nonempty → hausdorffDist K' K < η →
      ∀ p ∈ edge K' t, dist p (vtxP K t) < ε := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ², q = vtxP K t := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Set ℝ², S = K \ ball q (ε / 2) := ⟨_, rfl⟩
  have hScpt : IsCompact S := by
    rw [hS]
    exact hK.of_isClosed_subset (hK.isClosed.sdiff isOpen_ball) Set.sdiff_subset
  -- on `S` the linear functional `⟪·, u_t⟫` is bounded away from `h_K(t)`
  have hgap : ∃ c > 0, ∀ p ∈ S, ⟪p, u t⟫ ≤ supportFn K t - c := by
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · exact ⟨1, one_pos, fun p hp => absurd hp (by rw [hSe]; exact Set.notMem_empty p)⟩
    · obtain ⟨p₀, hp₀S, hp₀⟩ := exists_supportFn_eq hScpt hSne t
      have hlt : supportFn S t < supportFn K t := by
        rcases lt_or_eq_of_le (hp₀ ▸ le_supportFn hK (hS ▸ hp₀S).1 t) with h | h
        · exact h
        · exfalso
          have hedge : p₀ ∈ edge K t :=
            ⟨(hS ▸ hp₀S).1, show ⟪p₀, u t⟫ = supportFn K t by rw [hp₀]; exact h⟩
          rw [edge_eq_singleton hK hne hdeg, Set.mem_singleton_iff, ← hq] at hedge
          have : p₀ ∈ ball q (ε / 2) := by rw [hedge]; exact mem_ball_self (by linarith)
          exact (hS ▸ hp₀S).2 this
      exact ⟨supportFn K t - supportFn S t, by linarith,
        fun p hp => by have := le_supportFn hScpt hp t; linarith⟩
  obtain ⟨c, hc0, hcS⟩ := hgap
  refine ⟨min (ε / 2) (c / 3), lt_min (by linarith) (by linarith), ?_⟩
  intro K' hK'c hK'ne hd p hp
  have hd0 : 0 ≤ hausdorffDist K' K := hausdorffDist_nonneg
  have hdε : hausdorffDist K' K < ε / 2 := lt_of_lt_of_le hd (min_le_left _ _)
  have hdc : hausdorffDist K' K < c / 3 := lt_of_lt_of_le hd (min_le_right _ _)
  -- `p` almost attains `h_K(t)`
  have hpK' : ⟪p, u t⟫ = supportFn K' t := hp.2
  have habs := abs_supportFn_sub_le_hausdorffDist hK'c hK hK'ne hne t
  have hpu : supportFn K t - hausdorffDist K' K ≤ ⟪p, u t⟫ := by
    rw [hpK']; linarith [(abs_le.1 habs).1]
  -- pick a nearest point of `K`
  obtain ⟨q', hq'K, hpq'⟩ := hK.exists_infDist_eq_dist hne p
  have hdist : dist p q' ≤ hausdorffDist K' K := by
    rw [← hpq']
    exact infDist_le_hausdorffDist_of_mem (edge_subset K' t hp)
      (hausdorffEDist_ne_top_of_isCompact hK'c hK hK'ne hne)
  have hq'u : ⟪p, u t⟫ - dist p q' ≤ ⟪q', u t⟫ := by
    have h1 : ⟪p, u t⟫ - ⟪q', u t⟫ = ⟪p - q', u t⟫ := by rw [inner_sub_left]
    have h2 : ⟪p - q', u t⟫ ≤ ‖p - q'‖ := by
      calc ⟪p - q', u t⟫ ≤ ‖p - q'‖ * ‖u t‖ := real_inner_le_norm _ _
        _ = ‖p - q'‖ := by rw [norm_u, mul_one]
    rw [dist_eq_norm]; linarith
  -- so `q'` is close to `q`
  have hq'ball : q' ∈ ball q (ε / 2) := by
    by_contra hcon
    have hq'S : q' ∈ S := by rw [hS]; exact ⟨hq'K, hcon⟩
    have := hcS q' hq'S
    linarith
  calc dist p (vtxP K t) ≤ dist p q' + dist q' (vtxP K t) := dist_triangle _ _ _
    _ < ε := by
        rw [← hq]
        have hb := mem_ball.1 hq'ball
        linarith

/-! ## Convergence of the vertices, of `edgeMax` and of `arcFn` -/

theorem tendsto_vtxP_of_tendsto_hausdorffDist {ι : Type*} {l : Filter ι} {Ks : ι → Set ℝ²}
    (hKs : ∀ i, IsCompact (Ks i)) (hKsne : ∀ i, (Ks i).Nonempty) (hK : IsCompact K)
    (hne : K.Nonempty) (hlim : Tendsto (fun i => hausdorffDist (Ks i) K) l (𝓝 0)) {t : ℝ}
    (hdeg : edgeLength K t = 0) :
    Tendsto (fun i => vtxP (Ks i) t) l (𝓝 (vtxP K t)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη, hsub⟩ := exists_hausdorffDist_edge_subset_ball hK hne hdeg hε
  filter_upwards [(tendsto_order.1 hlim).2 η hη] with i hi
  exact hsub (Ks i) (hKs i) (hKsne i) hi _ (vtxP_mem_edge (hKs i) (hKsne i) t)

theorem tendsto_edgeMax_of_tendsto_hausdorffDist {ι : Type*} {l : Filter ι} {Ks : ι → Set ℝ²}
    (hKs : ∀ i, IsCompact (Ks i)) (hKsne : ∀ i, (Ks i).Nonempty) (hK : IsCompact K)
    (hne : K.Nonempty) (hlim : Tendsto (fun i => hausdorffDist (Ks i) K) l (𝓝 0)) {t : ℝ}
    (hdeg : edgeLength K t = 0) :
    Tendsto (fun i => edgeMax (Ks i) t) l (𝓝 (edgeMax K t)) := by
  have hcont : Continuous fun p : ℝ² => ⟪p, v t⟫ := continuous_id.inner continuous_const
  have h := (hcont.tendsto (vtxP K t)).comp
    (tendsto_vtxP_of_tendsto_hausdorffDist hKs hKsne hK hne hlim hdeg)
  simp only [Function.comp_def, inner_vtxP_v] at h
  exact h

/-- The primitive `t ↦ ∫_0^t h_{K_i}` converges pointwise (indeed uniformly on compacts). -/
theorem tendsto_primitive_of_tendsto_hausdorffDist {ι : Type*} {l : Filter ι} {Ks : ι → Set ℝ²}
    (hKs : ∀ i, IsCompact (Ks i)) (hKsne : ∀ i, (Ks i).Nonempty) (hK : IsCompact K)
    (hne : K.Nonempty) (hlim : Tendsto (fun i => hausdorffDist (Ks i) K) l (𝓝 0)) (t : ℝ) :
    Tendsto (fun i => ∫ s in (0:ℝ)..t, supportFn (Ks i) s) l
      (𝓝 (∫ s in (0:ℝ)..t, supportFn K s)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hpos : 0 < ε / (|t| + 1) := by positivity
  filter_upwards [(tendsto_order.1 hlim).2 (ε / (|t| + 1)) hpos] with i hi
  have hsub : (∫ s in (0:ℝ)..t, supportFn (Ks i) s) - ∫ s in (0:ℝ)..t, supportFn K s
      = ∫ s in (0:ℝ)..t, (supportFn (Ks i) s - supportFn K s) :=
    (intervalIntegral.integral_sub (integrable_supportFn (hKs i) (hKsne i) 0 t)
      (integrable_supportFn hK hne 0 t)).symm
  have hbd : ‖∫ s in (0:ℝ)..t, (supportFn (Ks i) s - supportFn K s)‖
      ≤ hausdorffDist (Ks i) K * |t - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => ?_
    rw [Real.norm_eq_abs]
    exact abs_supportFn_sub_le_hausdorffDist (hKs i) hK (hKsne i) hne s
  rw [Real.dist_eq, hsub, ← Real.norm_eq_abs]
  have ht : |t - 0| = |t| := by rw [sub_zero]
  rw [ht] at hbd
  have hd0 : 0 ≤ hausdorffDist (Ks i) K := hausdorffDist_nonneg
  have habs : (0:ℝ) ≤ |t| := abs_nonneg t
  have : hausdorffDist (Ks i) K * |t| < ε := by
    calc hausdorffDist (Ks i) K * |t| ≤ hausdorffDist (Ks i) K * (|t| + 1) := by nlinarith
      _ < (ε / (|t| + 1)) * (|t| + 1) := by
          exact mul_lt_mul_of_pos_right hi (by linarith)
      _ = ε := by field_simp
  linarith

/-- **Weak convergence of the surface area measures**: `arcFn K_i(t) → arcFn K(t)` at every
continuity point `t` of `arcFn K` (i.e. wherever `σ_K({t}) = |e_K(t)| = 0`).  By Helly's
selection/Lévy's criterion this is exactly weak convergence `σ_{K_i} → σ_K`. -/
theorem tendsto_arcFn_of_tendsto_hausdorffDist {ι : Type*} {l : Filter ι} {Ks : ι → Set ℝ²}
    (hKs : ∀ i, IsCompact (Ks i)) (hKsne : ∀ i, (Ks i).Nonempty) (hK : IsCompact K)
    (hne : K.Nonempty) (hlim : Tendsto (fun i => hausdorffDist (Ks i) K) l (𝓝 0)) {t : ℝ}
    (hdeg : edgeLength K t = 0) :
    Tendsto (fun i => arcFn (Ks i) t) l (𝓝 (arcFn K t)) := by
  have h1 := tendsto_edgeMax_of_tendsto_hausdorffDist hKs hKsne hK hne hlim hdeg
  have h2 := tendsto_primitive_of_tendsto_hausdorffDist hKs hKsne hK hne hlim t
  have h := h1.add h2
  have he : ∀ i, edgeMax (Ks i) t + ∫ s in (0:ℝ)..t, supportFn (Ks i) s = arcFn (Ks i) t := by
    intro i; rw [edgeMax_eq_arcFn_sub]; ring
  have he' : edgeMax K t + ∫ s in (0:ℝ)..t, supportFn K s = arcFn K t := by
    rw [edgeMax_eq_arcFn_sub]; ring
  simp only [he, he'] at h
  exact h

/-- Consequently `σ_{K_i}((a,b]) → σ_K((a,b])` whenever `a` and `b` are continuity points. -/
theorem tendsto_sigmaK_Ioc {ι : Type*} {l : Filter ι} {Ks : ι → Set ℝ²}
    (hKs : ∀ i, IsCompact (Ks i)) (hKsne : ∀ i, (Ks i).Nonempty) (hK : IsCompact K)
    (hne : K.Nonempty) (hlim : Tendsto (fun i => hausdorffDist (Ks i) K) l (𝓝 0)) {a b : ℝ}
    (hab : a ≤ b) (hda : edgeLength K a = 0) (hdb : edgeLength K b = 0) :
    Tendsto (fun i => (sigmaK (Ks i) (Ioc a b)).toReal) l
      (𝓝 (sigmaK K (Ioc a b)).toReal) := by
  have h := (tendsto_arcFn_of_tendsto_hausdorffDist hKs hKsne hK hne hlim hdb).sub
    (tendsto_arcFn_of_tendsto_hausdorffDist hKs hKsne hK hne hlim hda)
  have he : ∀ i, (sigmaK (Ks i) (Ioc a b)).toReal = arcFn (Ks i) b - arcFn (Ks i) a :=
    fun i => sigmaK_Ioc_toReal (hKs i) (hKsne i) hab
  simp only [he]
  rw [sigmaK_Ioc_toReal hK hne hab]
  exact h

end Sofa
