/-
# Sofa/CapThm.lean — the cap contains the niche (Baek §2.5, part 2)

* upper semicontinuity of the edge map `t ↦ e_K(t)` (replaces Thm 2.1.3 in Baek's argument);
* the upper boundary `δK` (Def 2.5.2), **Prop 2.5.1** (in the form "`z ∈ K` lies in `δK` iff
  every neighbourhood of `z` meets `F_ω \ K`"), **Prop 2.5.2** (`δK` is connected);
* **Thm 2.5.8** (four equivalent conditions for `N(K) ⊆ K`);
* **Thm 2.5.9** (`K` is the cap of a monotone sofa iff `N(K) ⊆ K`);
* the sofa area functional `A_ω(K) = |K| - |N(K)|` (Def 2.5.8) and **Thm 2.5.10**.

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 1 (2026-09-17, Opus 5): compiled in the cloud dev tree
(Lean 4.33.1, Mathlib v4.33.1 with subset imports), no `sorry`; full `import Mathlib` re-check pending.
-/
import Sofa.CapNiche

noncomputable section

open Real Set MovingSofa MeasureTheory Filter Topology
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa

variable {K : Set ℝ²} {ω : ℝ}

/-! ## Upper semicontinuity of the edge map -/

lemma continuous_inner_u_param : Continuous fun q : ℝ × ℝ² => ⟪q.2, u q.1⟫ :=
  continuous_snd.inner (continuous_u.comp continuous_fst)

lemma mem_edge_iff {p : ℝ²} {t : ℝ} : p ∈ edge K t ↔ p ∈ K ∧ ⟪p, u t⟫ = supportFn K t :=
  Iff.rfl

/-- The set of angles whose edge meets a given closed set is closed. -/
lemma isClosed_setOf_edge_meets (hK : IsCompact K) (hne : K.Nonempty) {F : Set ℝ²}
    (hF : IsClosed F) : IsClosed {t : ℝ | (edge K t ∩ F).Nonempty} := by
  have hKF : IsCompact (K ∩ F) := hK.inter_right hF
  have : CompactSpace (K ∩ F : Set ℝ²) := isCompact_iff_compactSpace.1 hKF
  have hc : Continuous fun q : ℝ × (K ∩ F : Set ℝ²) =>
      ⟪((q.2 : ℝ²)), u q.1⟫ - supportFn K q.1 := by
    have h1 : Continuous fun q : ℝ × (K ∩ F : Set ℝ²) => (q.1, (q.2 : ℝ²)) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    exact (continuous_inner_u_param.comp h1).sub
      ((continuous_supportFn hK hne).comp continuous_fst)
  have hZ : IsClosed {q : ℝ × (K ∩ F : Set ℝ²) |
      ⟪((q.2 : ℝ²)), u q.1⟫ - supportFn K q.1 = 0} :=
    isClosed_eq hc continuous_const
  have himg := isClosedMap_fst_of_compactSpace _ hZ
  convert himg using 1
  ext t
  simp only [mem_ofPred_eq, mem_image, Prod.exists, exists_and_right, exists_eq_right,
    Subtype.exists, mem_inter_iff, sub_eq_zero]
  constructor
  · rintro ⟨p, ⟨hpK, hpt⟩, hpF⟩
    exact ⟨p, ⟨hpK, hpF⟩, hpt⟩
  · rintro ⟨p, ⟨hpK, hpF⟩, hpt⟩
    exact ⟨p, ⟨hpK, hpt⟩, hpF⟩

/-- **Upper semicontinuity of edges**: `{t | e_K(t) ⊆ U}` is open for open `U`. -/
lemma isOpen_setOf_edge_subset (hK : IsCompact K) (hne : K.Nonempty) {U : Set ℝ²}
    (hU : IsOpen U) : IsOpen {t : ℝ | edge K t ⊆ U} := by
  have h := isClosed_setOf_edge_meets hK hne hU.isClosed_compl
  have e : {t : ℝ | edge K t ⊆ U} = {t : ℝ | (edge K t ∩ Uᶜ).Nonempty}ᶜ := by
    ext t
    simp only [mem_ofPred_eq, mem_compl_iff, inter_compl_nonempty_iff, not_not]
  rw [e]
  exact h.isOpen_compl

lemma convex_edge (hK : Convex ℝ K) (t : ℝ) : Convex ℝ (edge K t) :=
  hK.inter (convex_hyperplane (isLinearMap_inner_u t) _)

/-- A union of edges over an interval of angles is preconnected (Baek's proof of Prop 2.5.2). -/
theorem isPreconnected_biUnion_edge (hK : IsCompact K) (hKc : Convex ℝ K) (hne : K.Nonempty)
    (a b : ℝ) : IsPreconnected (⋃ t ∈ Icc a b, edge K t) := by
  intro U V hU hV hsub hU' hV'
  by_contra hcon
  -- each edge lies in `U` or in `V`
  have key : ∀ t ∈ Icc a b, edge K t ⊆ U ∨ edge K t ⊆ V := by
    intro t ht
    have he : edge K t ⊆ ⋃ t ∈ Icc a b, edge K t := subset_biUnion_of_mem ht
    by_contra hnot
    rw [not_or] at hnot
    obtain ⟨p, hp, hpU⟩ := not_subset.1 hnot.1
    obtain ⟨q, hq, hqV⟩ := not_subset.1 hnot.2
    have hpV : p ∈ V := (hsub (he hp)).resolve_left hpU
    have hqU : q ∈ U := (hsub (he hq)).resolve_right hqV
    obtain ⟨r, hr, hrUV⟩ := (convex_edge hKc t).isPreconnected U V hU hV (he.trans hsub)
      ⟨q, hq, hqU⟩ ⟨p, hp, hpV⟩
    exact hcon ⟨r, he hr, hrUV⟩
  obtain ⟨x, hxδ, hxU⟩ := hU'
  obtain ⟨y, hyδ, hyV⟩ := hV'
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hxδ
  obtain ⟨s', hs', hys'⟩ := mem_iUnion₂.1 hyδ
  have hsU : edge K s ⊆ U := by
    rcases key s hs with h | h
    · exact h
    · exact absurd ⟨x, hxδ, hxU, h hxs⟩ hcon
  have hs'V : edge K s' ⊆ V := by
    rcases key s' hs' with h | h
    · exact absurd ⟨y, hyδ, h hys', hyV⟩ hcon
    · exact h
  obtain ⟨τ, hτ, hτU, hτV⟩ := isPreconnected_Icc {t | edge K t ⊆ U} {t | edge K t ⊆ V}
    (isOpen_setOf_edge_subset hK hne hU) (isOpen_setOf_edge_subset hK hne hV)
    (fun t ht => key t ht) ⟨s, hs, hsU⟩ ⟨s', hs', hs'V⟩
  obtain ⟨z, hz⟩ := edge_nonempty hK hne τ
  exact hcon ⟨z, mem_biUnion hτ hz, hτU hz, hτV hz⟩

/-! ## The upper boundary (Def 2.5.2, Prop 2.5.1, Prop 2.5.2) -/

/-- **Def 2.5.2.** The upper boundary `δK = ⋃_{t ∈ [0, ω + π/2]} e_K(t)`. -/
def upperBdry (K : Set ℝ²) (ω : ℝ) : Set ℝ² := ⋃ t ∈ Icc (0 : ℝ) (ω + π / 2), edge K t

lemma mem_upperBdry_iff {z : ℝ²} :
    z ∈ upperBdry K ω ↔ ∃ t ∈ Icc (0 : ℝ) (ω + π / 2), z ∈ edge K t := by
  simp only [upperBdry, mem_iUnion₂, exists_prop]

lemma upperBdry_subset (K : Set ℝ²) (ω : ℝ) : upperBdry K ω ⊆ K :=
  iUnion₂_subset fun _ _ => inter_subset_left

lemma edge_subset_upperBdry {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (ω + π / 2)) :
    edge K t ⊆ upperBdry K ω :=
  subset_biUnion_of_mem (u := fun t => edge K t) ht

lemma Jω_subset_Icc : Jω ω ⊆ Icc (0 : ℝ) (ω + π / 2) := by
  rintro t (ht | ht)
  · exact ⟨ht.1, by linarith [ht.2, pi_pos]⟩
  · exact ⟨by linarith [ht.1, pi_pos], ht.2⟩

lemma isCompact_Jω (ω : ℝ) : IsCompact (Jω ω) := isCompact_Icc.union isCompact_Icc

/-- Moving from `F_ω` in a direction `u_t`, `t ∈ [0, ω + π/2]`, stays in `F_ω`. -/
lemma add_smul_u_mem_fan {z : ℝ²} (hz : z ∈ fan ω) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (ω + π / 2))
    (hω1 : ω ≤ π / 2) {ε : ℝ} (hε : 0 ≤ ε) : z + ε • u t ∈ fan ω := by
  obtain ⟨hz1, hz2⟩ := hz
  have hs : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2])
  have hc : 0 ≤ cos (t - ω) := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨?_, ?_⟩
  · simp only [PiLp.add_apply, PiLp.smul_apply, u_coord_one, smul_eq_mul]
    nlinarith
  · rw [inner_add_left, real_inner_smul_left, inner_u_u_eq_cos]
    nlinarith

lemma add_smul_u_not_mem (hK : IsCompact K) {z : ℝ²} {t : ℝ} (hz : z ∈ edge K t) {ε : ℝ}
    (hε : 0 < ε) : z + ε • u t ∉ K := by
  intro h
  have h1 := le_supportFn hK h t
  rw [inner_add_left, real_inner_smul_left, inner_u_u, mul_one, hz.2] at h1
  linarith

namespace IsCap

variable (hK : IsCap K ω)
include hK

/-- The upper boundary of a cap is connected (**Prop 2.5.2**). -/
theorem isConnected_upperBdry (hω0 : 0 ≤ ω) : IsConnected (upperBdry K ω) := by
  refine ⟨?_, isPreconnected_biUnion_edge hK.isCompact hK.convex hK.nonempty _ _⟩
  obtain ⟨z, hz⟩ := edge_nonempty hK.isCompact hK.nonempty 0
  exact ⟨z, edge_subset_upperBdry ⟨le_rfl, by linarith [pi_pos]⟩ hz⟩

lemma isClosed : IsClosed K := hK.isCompact.isClosed

/-- Points of `F_ω` violating a cap constraint violate one with angle in `J_ω`. -/
lemma exists_Jω_of_not_mem {q : ℝ²} (hq : q ∈ fan ω) (hqK : q ∉ K) :
    ∃ s ∈ Jω ω, supportFn K s < ⟪q, u s⟫ := by
  rw [hK.mem_iff] at hqK
  push Not at hqK
  obtain ⟨s, hs, hlt⟩ := hqK
  rcases hs with hs | hs
  · exact ⟨s, hs, hlt⟩
  · exfalso
    rcases hs with hs | hs
    · rw [hs, hK.supportFn_ω_add_pi, u_add_pi, inner_neg_right] at hlt
      linarith [hq.2]
    · rw [mem_singleton_iff] at hs
      rw [hs, hK.supportFn_three_pi_div_two, u_three_pi_div_two, inner_neg_right,
        inner_u_pi_div_two] at hlt
      linarith [hq.1]

/-- If `z ∈ K` is on no edge `e_K(t)`, `t ∈ J_ω`, then a whole neighbourhood of `z` in `F_ω` lies
in `K`. -/
lemma exists_ball_of_not_mem_edges {z : ℝ²} (hz : z ∈ K) (hω0 : 0 ≤ ω)
    (hne : ∀ t ∈ Jω ω, z ∉ edge K t) :
    ∃ m > 0, ∀ q ∈ fan ω, dist q z < m → q ∈ K := by
  have hcont : ContinuousOn (fun s => supportFn K s - ⟪z, u s⟫) (Jω ω) :=
    ((continuous_supportFn hK.isCompact hK.nonempty).sub
      ((continuous_const.inner continuous_u))).continuousOn
  have hJne : (Jω ω).Nonempty := ⟨0, Or.inl ⟨le_rfl, hω0⟩⟩
  obtain ⟨s₀, hs₀, hmin⟩ := (isCompact_Jω ω).exists_isMinOn hJne hcont
  have hmin' := isMinOn_iff.1 hmin
  have hm : 0 < supportFn K s₀ - ⟪z, u s₀⟫ := by
    have h1 : ⟪z, u s₀⟫ ≤ supportFn K s₀ := hK.inner_le hz s₀
    have h2 : ⟪z, u s₀⟫ ≠ supportFn K s₀ := fun h => hne s₀ hs₀ ⟨hz, h⟩
    exact sub_pos.2 (lt_of_le_of_ne h1 h2)
  refine ⟨_, hm, fun q hq hqd => ?_⟩
  by_contra hqK
  obtain ⟨s, hs, hlt⟩ := hK.exists_Jω_of_not_mem hq hqK
  have h1 : supportFn K s₀ - ⟪z, u s₀⟫ ≤ supportFn K s - ⟪z, u s⟫ := hmin' s hs
  have h2 : ⟪q, u s⟫ - ⟪z, u s⟫ ≤ ‖q - z‖ := by
    rw [← inner_sub_left]
    calc ⟪q - z, u s⟫ ≤ ‖q - z‖ * ‖u s‖ := real_inner_le_norm _ _
      _ = ‖q - z‖ := by rw [norm_u, mul_one]
  have h3 : ‖q - z‖ < supportFn K s₀ - ⟪z, u s₀⟫ := by rwa [← dist_eq_norm]
  linarith

/-- **Prop 2.5.1.** A point `z ∈ K` lies on the upper boundary `δK` iff it is a boundary point of
`K` relative to `F_ω`, i.e. every neighbourhood of `z` meets `F_ω \ K`. -/
theorem mem_upperBdry_iff_relFrontier (hω0 : 0 ≤ ω) (hω1 : ω ≤ π / 2) {z : ℝ²} (hz : z ∈ K) :
    z ∈ upperBdry K ω ↔ ∀ ε > 0, ∃ q ∈ fan ω, dist q z < ε ∧ q ∉ K := by
  constructor
  · intro hzδ ε hε
    obtain ⟨t, ht, hzt⟩ := mem_upperBdry_iff.1 hzδ
    refine ⟨z + (ε / 2) • u t,
      add_smul_u_mem_fan (hK.subset_fan hz) ht hω1 (by positivity), ?_,
      add_smul_u_not_mem hK.isCompact hzt (by positivity)⟩
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_u, mul_one, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    linarith
  · intro h
    by_contra hzδ
    have hne : ∀ t ∈ Jω ω, z ∉ edge K t := fun t ht hzt =>
      hzδ (edge_subset_upperBdry (Jω_subset_Icc ht) hzt)
    obtain ⟨m, hm, hball⟩ := hK.exists_ball_of_not_mem_edges hz hω0 hne
    obtain ⟨q, hq, hqd, hqK⟩ := h m hm
    exact hqK (hball q hq hqd)

/-- **Prop 2.5.1** as a set identity. -/
theorem upperBdry_eq_relFrontier (hω0 : 0 ≤ ω) (hω1 : ω ≤ π / 2) :
    upperBdry K ω = {z ∈ K | ∀ ε > 0, ∃ q ∈ fan ω, dist q z < ε ∧ q ∉ K} := by
  ext z
  constructor
  · intro hz
    have hzK := upperBdry_subset K ω hz
    exact ⟨hzK, (hK.mem_upperBdry_iff_relFrontier hω0 hω1 hzK).1 hz⟩
  · rintro ⟨hzK, h⟩
    exact (hK.mem_upperBdry_iff_relFrontier hω0 hω1 hzK).2 h

end IsCap

/-! ## Auxiliary facts for Theorem 2.5.8 -/

lemma interior_fan (ω : ℝ) : interior (fan ω) = {p | 0 < p 1 ∧ 0 < ⟪p, u ω⟫} := by
  apply Subset.antisymm
  · intro p hp
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hp)
    have hd : ∀ w : ℝ², ‖w‖ = 1 → p - (ε / 2) • w ∈ fan ω := by
      intro w hw
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hw, mul_one,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have h1 := (hd (u (π / 2)) (norm_u _)).1
    have h2 := (hd (u ω) (norm_u _)).2
    simp only [PiLp.sub_apply, PiLp.smul_apply, u_coord_one, sin_pi_div_two, smul_eq_mul,
      mul_one] at h1
    rw [inner_sub_left, real_inner_smul_left, inner_u_u, mul_one] at h2
    exact ⟨by linarith, by linarith⟩
  · apply interior_maximal
    · rintro p ⟨h1, h2⟩
      exact ⟨h1.le, h2.le⟩
    · exact (isOpen_lt continuous_const (continuous_coord 1)).inter
        (isOpen_lt continuous_const (continuous_inner_u ω))

lemma isClosed_fan (ω : ℝ) : IsClosed (fan ω) :=
  (isClosed_le continuous_const (continuous_coord 1)).inter
    (isClosed_le continuous_const (continuous_inner_u ω))

/-- `q 1 = ⟪q, u_t⟫ sin t + ⟪q, v_t⟫ cos t`. -/
lemma coord_one_decomp (q : ℝ²) (t : ℝ) : q 1 = ⟪q, u t⟫ * sin t + ⟪q, v t⟫ * cos t := by
  simp only [inner_eq, u_coord_zero, u_coord_one, v_coord_zero, v_coord_one]
  linear_combination (-q 1) * sin_sq_add_cos_sq t

/-- `⟪q, u_ω⟫ = ⟪q, u_t⟫ cos (ω - t) + ⟪q, v_t⟫ sin (ω - t)`. -/
lemma inner_u_decomp' (q : ℝ²) (ω t : ℝ) :
    ⟪q, u ω⟫ = ⟪q, u t⟫ * cos (ω - t) + ⟪q, v t⟫ * sin (ω - t) := by
  simp only [inner_eq, u_coord_zero, u_coord_one, v_coord_zero, v_coord_one, sin_sub, cos_sub]
  linear_combination (-(q 0 * cos ω + q 1 * sin ω)) * sin_sq_add_cos_sq t

lemma inner_v_zero (q : ℝ²) : ⟪q, v 0⟫ = q 1 := by
  rw [v_zero_eq, inner_u_pi_div_two]

/-- If the inner corner `x_K(t)` is not in the interior of the fan, the wedge `T_K(t)` is empty. -/
lemma wedge_eq_empty {t : ℝ} (ht : t ∈ Ioo 0 ω) (hω1 : ω ≤ π / 2)
    (hx : innerCorner K t 1 ≤ 0 ∨ ⟪innerCorner K t, u ω⟫ ≤ 0) : wedge K ω t = ∅ := by
  obtain ⟨hs, hc, -, hsw, hcw, -⟩ := trig_facts ht hω1
  rw [eq_empty_iff_forall_notMem]
  rintro p ⟨⟨hp1, hpω⟩, hpQ⟩
  rw [mem_QminusS_iff, u_add_pi_div_two] at hpQ
  have hxu := inner_innerCorner_u (S := K) t
  have hxv := inner_innerCorner_v (S := K) t
  rcases hx with hx | hx
  · rw [coord_one_decomp _ t, hxu, hxv] at hx
    rw [coord_one_decomp _ t] at hp1
    nlinarith [mul_lt_mul_of_pos_right hpQ.1 hs, mul_lt_mul_of_pos_right hpQ.2 hc]
  · rw [inner_u_decomp' _ ω t, hxu, hxv] at hx
    rw [inner_u_decomp' _ ω t] at hpω
    nlinarith [mul_lt_mul_of_pos_right hpQ.1 hcw, mul_lt_mul_of_pos_right hpQ.2 hsw]

/-- The niche is closed in the direction `-v₀` (relative to `F_ω`). -/
lemma mem_niche_of_add_smul_v_zero (hω1 : ω ≤ π / 2) {p : ℝ²} (hp : p ∈ fan ω) {r : ℝ}
    (hr : 0 ≤ r) (h : p + r • v 0 ∈ niche K ω) : p ∈ niche K ω := by
  obtain ⟨-, t, ht, hQ⟩ := mem_niche_iff.1 h
  refine mem_niche_iff.2 ⟨hp, t, ht, ?_⟩
  have hd := dir_neg_v_zero hω1 t (Ioo_subset_Icc_self ht)
  have := closedDir_QminusS (S := K) hd.1 hd.2 _ hQ r hr
  rwa [smul_neg, add_neg_cancel_right] at this

namespace IsCap

variable (hK : IsCap K ω)
include hK

/-- `F_ω \ K` is closed in the direction `v₀`. -/
lemma add_smul_v_zero_not_mem (hω1 : ω ≤ π / 2) {x : ℝ²} (hx : x ∈ fan ω) (hxK : x ∉ K)
    {r : ℝ} (hr : 0 ≤ r) : x + r • v 0 ∉ K := by
  obtain ⟨s, hs, hlt⟩ := hK.exists_Jω_of_not_mem hx hxK
  intro hmem
  have h := hK.inner_le hmem s
  have hsin : 0 ≤ sin s := by
    rcases hs with hs | hs
    · exact sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2, pi_pos])
    · exact sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.1, pi_pos]) (by linarith [hs.2])
  rw [inner_add_left, real_inner_smul_left, inner_v_u_eq_sin, sub_zero] at h
  nlinarith [mul_nonneg hr hsin]

/-- Every point of a cap lies below a point of the upper boundary. -/
lemma exists_top (hω0 : 0 < ω) (hω1 : ω ≤ π / 2) {p : ℝ²} (hp : p ∈ K) :
    ∃ r : ℝ, 0 ≤ r ∧ p + r • v 0 ∈ upperBdry K ω := by
  have hcont : Continuous fun r : ℝ => p + r • v 0 := by fun_prop
  obtain ⟨R, hR⟩ : ∃ R : Set ℝ, R = Ici 0 ∩ (fun r : ℝ => p + r • v 0) ⁻¹' K := ⟨_, rfl⟩
  have hRmem : ∀ r, r ∈ R ↔ 0 ≤ r ∧ p + r • v 0 ∈ K := by
    intro r; rw [hR]; rfl
  have hRc : IsClosed R := by
    rw [hR]; exact isClosed_Ici.inter (hK.isClosed.preimage hcont)
  have h0R : (0 : ℝ) ∈ R := (hRmem 0).2 ⟨le_rfl, by simpa using hp⟩
  have hRb : BddAbove R := by
    refine ⟨1 - p 1, fun r hr => ?_⟩
    have hr' := (hRmem r).1 hr
    have h1 := (hK.subset_para hr'.2).1.2
    have h2 := (hK.subset_para hp).1.1
    simp only [PiLp.add_apply, PiLp.smul_apply, v_coord_one, cos_zero, smul_eq_mul,
      mul_one] at h1
    linarith
  obtain ⟨r₀, hr₀⟩ : ∃ r₀, r₀ = sSup R := ⟨_, rfl⟩
  have hmem : r₀ ∈ R := hr₀ ▸ hRc.csSup_mem ⟨0, h0R⟩ hRb
  have hmem' := (hRmem r₀).1 hmem
  refine ⟨r₀, hmem'.1, ?_⟩
  by_contra hδ
  have hne : ∀ t ∈ Jω ω, p + r₀ • v 0 ∉ edge K t := fun t ht hzt =>
    hδ (edge_subset_upperBdry (Jω_subset_Icc ht) hzt)
  obtain ⟨m, hm, hball⟩ := hK.exists_ball_of_not_mem_edges hmem'.2 hω0.le hne
  have hq : p + (r₀ + m / 2) • v 0 ∈ K := by
    apply hball
    · have := add_smul_u_mem_fan (hK.subset_fan hmem'.2) (t := π / 2)
        ⟨by linarith [pi_pos], by linarith⟩ hω1 (ε := m / 2) (by positivity)
      rw [← v_zero_eq] at this
      convert this using 1
      rw [add_smul, add_assoc]
    · rw [dist_eq_norm, add_smul, ← add_assoc, add_sub_cancel_left, norm_smul, v_zero_eq,
        norm_u, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
  have hle : r₀ + m / 2 ≤ r₀ := by
    rw [hr₀]
    apply le_csSup hRb
    rw [← hr₀]
    exact (hRmem _).2 ⟨by linarith [hmem'.1], hq⟩
  linarith

/-- **Theorem 2.5.8.** Four equivalent conditions for a cap `K` to contain its niche. -/
theorem tfae_niche_subset (hω0 : 0 < ω) (hω1 : ω ≤ π / 2) :
    List.TFAE [niche K ω ⊆ K,
      niche K ω ⊆ K \ upperBdry K ω,
      ∀ t ∈ Ioo 0 ω, innerCorner K t ∉ interior (fan ω) ∨ innerCorner K t ∈ K,
      IsConnected (K \ niche K ω)] := by
  tfae_have 2 → 1 := fun h2 => h2.trans sdiff_subset
  tfae_have 1 → 2 := by
    intro h1 z hz
    refine ⟨h1 hz, fun hzδ => ?_⟩
    obtain ⟨hzF, s, hs, hzQ⟩ := mem_niche_iff.1 hz
    obtain ⟨t, ht, hzt⟩ := mem_upperBdry_iff.1 hzδ
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isOpen_QminusS K s) z hzQ
    have hq : z + (δ / 2) • u t ∈ QminusS K s := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_u, mul_one,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have hqN : z + (δ / 2) • u t ∈ niche K ω :=
      mem_niche_iff.2 ⟨add_smul_u_mem_fan hzF ht hω1 (by positivity), s, hs, hq⟩
    exact add_smul_u_not_mem hK.isCompact hzt (by positivity) (h1 hqN)
  tfae_have 3 → 1 := by
    intro h3 p hp
    rw [niche_eq_iUnion_wedge, mem_iUnion₂] at hp
    obtain ⟨t, ht, hpt⟩ := hp
    rcases h3 t ht with hx | hx
    · rw [interior_fan] at hx
      have hx' : innerCorner K t 1 ≤ 0 ∨ ⟪innerCorner K t, u ω⟫ ≤ 0 := by
        by_contra hcon
        push Not at hcon
        exact hx hcon
      rw [wedge_eq_empty ht hω1 hx'] at hpt
      exact absurd hpt (notMem_empty p)
    · exact hK.wedge_subset hω0 hω1 ht hx hpt
  tfae_have 1 → 3 := by
    intro h1 t ht
    rw [interior_fan, or_iff_not_imp_left, not_not]
    rintro ⟨hx1, hxω⟩
    by_contra hxK
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl _ hxK
    obtain ⟨hs, hc, -, -, -, -⟩ := trig_facts ht hω1
    have hm : 0 < min (min (innerCorner K t 1) ⟪innerCorner K t, u ω⟫) δ :=
      lt_min (lt_min hx1 hxω) hδ
    obtain ⟨ε, hε, hε1, hε2, hε3⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < innerCorner K t 1 ∧
        ε < ⟪innerCorner K t, u ω⟫ ∧ ε < δ := by
      refine ⟨_, half_pos hm, ?_, ?_, ?_⟩
      · linarith [min_le_left (min (innerCorner K t 1) ⟪innerCorner K t, u ω⟫) δ,
          min_le_left (innerCorner K t 1) ⟪innerCorner K t, u ω⟫]
      · linarith [min_le_left (min (innerCorner K t 1) ⟪innerCorner K t, u ω⟫) δ,
          min_le_right (innerCorner K t 1) ⟪innerCorner K t, u ω⟫]
      · linarith [min_le_right (min (innerCorner K t 1) ⟪innerCorner K t, u ω⟫) δ]
    have hpK : innerCorner K t + (-ε) • v 0 ∉ K := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, v_zero_eq, norm_u,
        mul_one, Real.norm_eq_abs, abs_neg, abs_of_pos hε]
      exact hε3
    apply hpK
    apply h1
    have hsω : sin ω ≤ 1 := sin_le_one ω
    refine mem_niche_iff.2 ⟨⟨?_, ?_⟩, t, ht, ?_⟩
    · simp only [PiLp.add_apply, PiLp.smul_apply, v_coord_one, cos_zero, smul_eq_mul]
      linarith
    · rw [inner_add_left, real_inner_smul_left, inner_v_u_eq_sin, sub_zero]
      nlinarith
    · rw [mem_QminusS_iff, u_add_pi_div_two, inner_add_left, inner_add_left,
        real_inner_smul_left, real_inner_smul_left, inner_v_u_eq_sin, inner_v_v_eq_cos,
        sub_zero, inner_innerCorner_u, inner_innerCorner_v]
      constructor <;> nlinarith
  tfae_have 2 → 4 := by
    intro h2
    have hδS : upperBdry K ω ⊆ K \ niche K ω := fun z hz =>
      ⟨upperBdry_subset K ω hz, fun hzN => (h2 hzN).2 hz⟩
    have hδ := hK.isConnected_upperBdry hω0.le
    obtain ⟨x₀, hx₀⟩ := hδ.nonempty
    refine ⟨hδ.nonempty.mono hδS, isPreconnected_of_forall x₀ fun y hy => ?_⟩
    obtain ⟨r, hr, hzδ⟩ := hK.exists_top hω0 hω1 hy.1
    refine ⟨segment ℝ y (y + r • v 0) ∪ upperBdry K ω, union_subset ?_ hδS, Or.inr hx₀,
      Or.inl (left_mem_segment _ _ _),
      (convex_segment _ _).isPreconnected.union (y + r • v 0) (right_mem_segment _ _ _) hzδ
        hδ.isPreconnected⟩
    intro q hq
    have hqK : q ∈ K := hK.convex.segment_subset hy.1 (upperBdry_subset K ω hzδ) hq
    refine ⟨hqK, fun hqN => hy.2 ?_⟩
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hq
    obtain rfl : a = 1 - b := by linarith
    have e : (1 - b) • y + b • (y + r • v 0) = y + (b * r) • v 0 := by module
    rw [e] at hqN
    exact mem_niche_of_add_smul_v_zero hω1 (hK.subset_fan hy.1) (mul_nonneg hb hr) hqN
  tfae_have 4 → 3 := by
    intro h4 t ht
    rw [interior_fan, or_iff_not_imp_left, not_not]
    rintro ⟨hx1, hxω⟩
    by_contra hxK
    obtain ⟨hs, hc, -, hsw, hcw, -⟩ := trig_facts ht hω1
    have hxu := inner_innerCorner_u (S := K) t
    have hxv := inner_innerCorner_v (S := K) t
    -- no point of `K \ N(K)` on the vertical line through `x_K(t)`
    have hline : ∀ p ∈ K \ niche K ω, p 0 ≠ innerCorner K t 0 := by
      rintro p ⟨hpK, hpN⟩ hp0
      have hpe : p = innerCorner K t + (p 1 - innerCorner K t 1) • v 0 := by
        ext i
        fin_cases i
        · simp [v, hp0]
        · simp [v]
      rcases le_or_gt (innerCorner K t 1) (p 1) with hle | hlt
      · exact hK.add_smul_v_zero_not_mem hω1 ⟨hx1.le, hxω.le⟩ hxK (sub_nonneg.2 hle)
          (hpe ▸ hpK)
      · apply hpN
        refine mem_niche_iff.2 ⟨hK.subset_fan hpK, t, ht, ?_⟩
        rw [mem_QminusS_iff, u_add_pi_div_two, hpe, inner_add_left, inner_add_left,
          real_inner_smul_left, real_inner_smul_left, inner_v_u_eq_sin, inner_v_v_eq_cos,
          sub_zero, hxu, hxv]
        constructor <;> nlinarith
    -- the corners are on opposite sides of that line
    have hA := hK.cornerA_mem hω0 hω1
    have hAN := hK.cornerA_not_mem_niche hω1
    have hC := hK.cornerC_mem hω0 hω1
    have hCN := hK.cornerC_not_mem_niche hω1
    have hA0 : innerCorner K t 0 < hK.cornerA 0 := by
      have hW := hK.gapW_pos hω1 ht
      rw [gapW, sub_pos, div_lt_iff₀ hc] at hW
      have e := inner_u_decomp (innerCorner K t) t
      rw [hxu] at e
      rw [hK.cornerA_eq, pt_zero]
      have key : innerCorner K t 0 * cos t < supportFn K 0 * cos t := by
        nlinarith [mul_pos hx1 hs]
      exact lt_of_mul_lt_mul_right key hc.le
    have hC0 : hK.cornerC 0 < innerCorner K t 0 := by
      have hZ := hK.gapZ_pos hω1 ht
      rw [gapZ, sub_pos, div_lt_iff₀ hcw] at hZ
      have hsinω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
      have e1 : ⟪innerCorner K t, v t⟫ =
          -(innerCorner K t 0) * sin t + innerCorner K t 1 * cos t := by
        simp only [inner_eq, v_coord_zero, v_coord_one]; ring
      have e2 := inner_u_decomp (innerCorner K t) ω
      have e3 : cos (ω - t) = cos ω * cos t + sin ω * sin t := cos_sub ω t
      have hC0e : hK.cornerC 0 = -(supportFn K (ω + π / 2) * sin ω) := by
        simp [cornerC, v]
      rw [hC0e]
      have iden : (innerCorner K t 0 + supportFn K (ω + π / 2) * sin ω) * cos (ω - t) -
          cos t * ⟪innerCorner K t, u ω⟫ =
          sin ω * (supportFn K (ω + π / 2) * cos (ω - t) - ⟪innerCorner K t, v t⟫) := by
        rw [e1, e2, e3]; ring
      rw [hxv] at iden
      have key : 0 < (innerCorner K t 0 + supportFn K (ω + π / 2) * sin ω) * cos (ω - t) := by
        nlinarith [mul_pos hc hxω, mul_pos hsinω (sub_pos.2 hZ)]
      have := pos_of_mul_pos_left key hcw.le
      linarith
    obtain ⟨-, hpre⟩ := h4
    obtain ⟨z, hzS, hz1, hz2⟩ := hpre {p | p 0 < innerCorner K t 0}
      {p | innerCorner K t 0 < p 0}
      (isOpen_lt (continuous_coord 0) continuous_const)
      (isOpen_lt continuous_const (continuous_coord 0))
      (fun p hp => lt_or_gt_of_ne (hline p hp)) ⟨hK.cornerC, ⟨hC, hCN⟩, hC0⟩
      ⟨hK.cornerA, ⟨hA, hAN⟩, hA0⟩
    have h1' : z 0 < innerCorner K t 0 := hz1
    have h2' : innerCorner K t 0 < z 0 := hz2
    exact lt_asymm h1' h2'
  tfae_finish

/-- `C(K) = K` for a cap `K`. -/
lemma Ccap_self : Ccap K ω = K := by
  apply Subset.antisymm
  · intro p hp
    obtain ⟨hP, hQ⟩ := mem_Ccap_iff.1 hp
    rw [hK.mem_iff]
    intro s hs
    rcases hs with (hs | hs) | hs | hs
    · exact (hQ s hs).1
    · have h := (hQ (s - π / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩).2
      rwa [sub_add_cancel] at h
    · rw [hs, hK.supportFn_ω_add_pi, u_add_pi, inner_neg_right, neg_nonpos]
      exact hP.2.1
    · rw [mem_singleton_iff] at hs
      rw [hs, hK.supportFn_three_pi_div_two, u_three_pi_div_two, inner_neg_right, neg_nonpos,
        inner_u_pi_div_two]
      exact hP.1.1
  · intro p hp
    exact mem_Ccap_iff.2 ⟨hK.subset_para hp, fun t _ => ⟨hK.inner_le hp t, hK.inner_le hp _⟩⟩

end IsCap

/-- `I(S) = C(S) \ N(S)` for any `S` in standard position (the set-theoretic core of
Thm 2.4.2 / Equation (2.1)). -/
lemma Imono_eq_Ccap_sdiff_niche {S : Set ℝ²} (hstd : StdPos S ω) :
    Imono S ω = Ccap S ω \ niche S ω := by
  ext p
  simp only [Set.mem_sdiff, mem_Imono_iff, mem_Ccap_iff, mem_niche_iff, suppHallway_eq]
  constructor
  · rintro ⟨hP, hL⟩
    refine ⟨⟨hP, fun t ht => (hL t ht).1⟩, ?_⟩
    rintro ⟨-, t, ht, hpt⟩
    exact (hL t (Ioo_subset_Icc_self ht)).2 hpt
  · rintro ⟨⟨hP, hQp⟩, hN⟩
    refine ⟨hP, fun t ht => ⟨hQp t ht, fun hpt => ?_⟩⟩
    rcases ht.1.lt_or_eq with ht0 | ht0
    · rcases ht.2.lt_or_eq with ht1 | ht1
      · exact hN ⟨para_subset_fan ω hP, t, ⟨ht0, ht1⟩, hpt⟩
      · subst ht1
        have := hpt.1
        simp only [hpLt, mem_ofPred_eq, hstd.1, sub_self] at this
        exact absurd hP.2.1 (not_le.2 this)
    · subst ht0
      have := hpt.2
      simp only [hpLt, mem_ofPred_eq, zero_add, hstd.2, sub_self, inner_u_pi_div_two] at this
      exact absurd hP.1.1 (not_le.2 this)

/-! ## Theorem 2.5.9 -/

/-- **Theorem 2.5.9.** A cap `K` is the cap of a monotone sofa iff it contains its niche.
(In the forward direction the monotone sofa is `K \ N(K)`.) -/
theorem IsCap.niche_subset_iff (hK : IsCap K ω) (hω0 : 0 < ω) (hω1 : ω ≤ π / 2) :
    niche K ω ⊆ K ↔ ∃ T, IsMonotoneSofa T ω ∧ Ccap T ω = K := by
  have tfae := hK.tfae_niche_subset hω0 hω1
  constructor
  · intro h1
    have h2 := (tfae.out 0 1).1 h1
    have h4 := (tfae.out 0 3).1 h1
    have hstdK : StdPos K ω := ⟨hK.supportFn_ω, hK.supportFn_pi_div_two⟩
    have hTeq : K \ niche K ω = Imono K ω := by
      rw [Imono_eq_Ccap_sdiff_niche hstdK, hK.Ccap_self]
    have hδS : upperBdry K ω ⊆ K \ niche K ω := fun z hz =>
      ⟨upperBdry_subset K ω hz, fun hzN => (h2 hzN).2 hz⟩
    have hTc : IsClosed (K \ niche K ω) := by rw [hTeq]; exact isClosed_Imono K ω
    have hTK : K \ niche K ω ⊆ K := sdiff_subset
    have hTcpt : IsCompact (K \ niche K ω) := hK.isCompact.of_isClosed_subset hTc hTK
    have hTne : (K \ niche K ω).Nonempty := h4.nonempty
    have hJ : ∀ s ∈ Jω ω, supportFn (K \ niche K ω) s = supportFn K s := by
      intro s hs
      apply le_antisymm (supportFn_mono hK.isCompact hTne hTK s)
      obtain ⟨z, hz⟩ := edge_nonempty hK.isCompact hK.nonempty s
      rw [← hz.2]
      exact le_supportFn hTcpt (hδS (edge_subset_upperBdry (Jω_subset_Icc hs) hz)) s
    have hstdT : StdPos (K \ niche K ω) ω :=
      ⟨by rw [hJ ω (Or.inl ⟨hω0.le, le_rfl⟩), hK.supportFn_ω],
        by rw [hJ (π / 2) (Or.inr ⟨le_rfl, by linarith⟩), hK.supportFn_pi_div_two]⟩
    have hTL : ∀ t ∈ Icc (0 : ℝ) ω, K \ niche K ω ⊆ suppHallway K t := by
      intro t ht p hp
      rw [hTeq] at hp
      exact (mem_Imono_iff.1 hp).2 t ht
    have hsofa : IsSofaWithAngle (K \ niche K ω) ω :=
      isSofaWithAngle_of_subset_suppHallway hK.isCompact hK.nonempty hω0.le hstdK h4 hTc
        (hTK.trans hK.subset_para) hTL
    refine ⟨K \ niche K ω, ⟨K \ niche K ω, hsofa, hstdT, ?_⟩, ?_⟩
    · rw [Imono_congr hJ, hTeq]
    · rw [Ccap_congr hJ, hK.Ccap_self]
  · rintro ⟨T, hT, hTK⟩
    have hTeq := hT.eq_Ccap_sdiff_niche hω0 hω1
    rw [hTK] at hTeq
    have hconn : IsConnected (K \ niche K ω) := by
      rw [← hTeq]; exact (hT.isSofaWithAngle hω0 hω1).isConnected
    exact (tfae.out 0 3).2 hconn

/-! ## The sofa area functional (Def 2.5.8, Thm 2.5.10) -/

/-- **Def 2.5.8.** The sofa area functional `A_ω(K) = |K| - |N(K)|`. -/
def sofaArea (K : Set ℝ²) (ω : ℝ) : ℝ := (volume K).toReal - (volume (niche K ω)).toReal

lemma isOpen_iUnion_QminusS (K : Set ℝ²) (ω : ℝ) :
    IsOpen (⋃ t ∈ Ioo (0 : ℝ) ω, QminusS K t) :=
  isOpen_biUnion fun t _ => isOpen_QminusS K t

lemma measurableSet_niche (K : Set ℝ²) (ω : ℝ) : MeasurableSet (niche K ω) :=
  (isClosed_fan ω).measurableSet.inter (isOpen_iUnion_QminusS K ω).measurableSet

lemma IsMonotoneSofa.stdPos {T : Set ℝ²} (hT : IsMonotoneSofa T ω) (hω0 : 0 < ω)
    (hω1 : ω ≤ π / 2) : StdPos T ω := by
  obtain ⟨S, hS, hstd, rfl⟩ := hT
  exact (hS.Imono_props hstd hω0 hω1).2.1

/-- The cap of a monotone sofa is a cap. -/
lemma IsMonotoneSofa.isCap_Ccap {T : Set ℝ²} (hT : IsMonotoneSofa T ω) (hω0 : 0 < ω)
    (hω1 : ω ≤ π / 2) : IsCap (Ccap T ω) ω :=
  (hT.isSofaWithAngle hω0 hω1).isCap_Ccap (hT.stdPos hω0 hω1) hω0 hω1

/-- **Theorem 2.5.10** (measure form): `|S| = |K| - |N(K)|` for the cap `K = C(S)` of a
monotone sofa `S`, and `N(K) ⊆ K`. -/
theorem IsMonotoneSofa.volume_eq {T : Set ℝ²} (hT : IsMonotoneSofa T ω) (hω0 : 0 < ω)
    (hω1 : ω ≤ π / 2) :
    niche (Ccap T ω) ω ⊆ Ccap T ω ∧
      volume T = volume (Ccap T ω) - volume (niche (Ccap T ω) ω) := by
  have hK := hT.isCap_Ccap hω0 hω1
  have hN : niche (Ccap T ω) ω ⊆ Ccap T ω := (hK.niche_subset_iff hω0 hω1).2 ⟨T, hT, rfl⟩
  have hfin : volume (Ccap T ω) ≠ ⊤ := (isCompact_Ccap hω0 hω1).measure_lt_top.ne
  refine ⟨hN, ?_⟩
  conv_lhs => rw [hT.eq_Ccap_sdiff_niche hω0 hω1]
  exact measure_sdiff hN (measurableSet_niche _ _).nullMeasurableSet
    (ne_top_of_le_ne_top hfin (measure_mono hN))

/-- **Theorem 2.5.10.** `A_ω(C(S)) = |S|` for a monotone sofa `S` with rotation angle `ω`. -/
theorem IsMonotoneSofa.sofaArea_Ccap {T : Set ℝ²} (hT : IsMonotoneSofa T ω) (hω0 : 0 < ω)
    (hω1 : ω ≤ π / 2) : sofaArea (Ccap T ω) ω = (volume T).toReal := by
  obtain ⟨hN, hvol⟩ := hT.volume_eq hω0 hω1
  have hfin : volume (Ccap T ω) ≠ ⊤ := (isCompact_Ccap hω0 hω1).measure_lt_top.ne
  rw [hvol, ENNReal.toReal_sub_of_le (measure_mono hN) hfin, sofaArea]

end Sofa
