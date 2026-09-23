/-
# Sofa/Vertex.lean — vertices of planar convex bodies (Baek Def 2.1.10, 2.1.14, Thm 2.1.3)

For a nonempty compact `K ⊆ ℝ²` and an angle `t`, the edge `e_K(t) = K ∩ l_K(t)` is a compact
subset of the line `l_K(t)` (direction `v_t`).  Its two extreme points in the direction `±v_t` are
the vertices `v⁺_K(t)` (`vtxP`) and `v⁻_K(t)` (`vtxM`); for convex `K` the edge is the segment
between them (`edge_eq_segment`).

Main results:
* the "monotonicity of edges": for `0 < s - t ≤ π/2`, `e_K(s)` lies beyond `e_K(t)` in the
  direction `v_t` (`inner_v_le_of_mem_edge`), and symmetrically;
* **Thm 2.1.3**: `v⁺_K(s), v⁻_K(s), v_K(t,s) → v⁺_K(t)` as `s → t⁺`, and
  `v⁺_K(s), v⁻_K(s), v_K(s,t) → v⁻_K(t)` as `s → t⁻`; in fact all edges `e_K(s)` shrink to the
  vertex (`eventually_edge_subset_ball_right/left`);
* the one-sided derivatives of the support function: `h'_K(t⁺) = ⟪v⁺_K(t), v_t⟫`,
  `h'_K(t⁻) = ⟪v⁻_K(t), v_t⟫`.

The proofs use only the upper semicontinuity of `t ↦ e_K(t)` (`isOpen_setOf_edge_subset`).

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 1 (2026-09-17, Opus 5): compiled in the cloud dev tree
(Lean 4.33.1, Mathlib v4.33.1 with subset imports), no `sorry`; full `import Mathlib` re-check pending.
-/
import Sofa.CapThm

noncomputable section

open Real Set Filter Topology
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²}

/-! ## Definitions -/

/-- `m⁺_K(t) = max {⟪p, v_t⟫ : p ∈ e_K(t)}`. -/
def edgeMax (K : Set ℝ²) (t : ℝ) : ℝ := supportFn (edge K t) (t + π / 2)

/-- `m⁻_K(t) = min {⟪p, v_t⟫ : p ∈ e_K(t)}`. -/
def edgeMin (K : Set ℝ²) (t : ℝ) : ℝ := -supportFn (edge K t) (t + π / 2 + π)

/-- **Def 2.1.10.** The vertex `v⁺_K(t)`: the end of the edge `e_K(t)` furthest in direction
`v_t`. -/
def vtxP (K : Set ℝ²) (t : ℝ) : ℝ² := supportFn K t • u t + edgeMax K t • v t

/-- **Def 2.1.10.** The vertex `v⁻_K(t)`: the end of the edge `e_K(t)` furthest in direction
`-v_t`. -/
def vtxM (K : Set ℝ²) (t : ℝ) : ℝ² := supportFn K t • u t + edgeMin K t • v t

/-- The length of the edge `e_K(t)` (for polygons this is `σ_K({t})`). -/
def edgeLength (K : Set ℝ²) (t : ℝ) : ℝ := edgeMax K t - edgeMin K t

/-- **Def 2.1.14.** `v_K(a, b) = l_K(a) ∩ l_K(b)` (for `b - a ∉ πℤ`). -/
def vtx2 (K : Set ℝ²) (a b : ℝ) : ℝ² :=
  supportFn K a • u a + ((supportFn K b - supportFn K a * cos (b - a)) / sin (b - a)) • v a

/-! ## Basic facts -/

lemma norm_v (t : ℝ) : ‖v t‖ = 1 := by rw [← u_add_pi_div_two, norm_u]

lemma u_add_pi_div_two_add_pi (t : ℝ) : u (t + π / 2 + π) = -v t := by
  rw [u_add_pi, u_add_pi_div_two]

lemma isCompact_edge (hK : IsCompact K) (t : ℝ) : IsCompact (edge K t) :=
  hK.inter_right (isClosed_line _ _)

lemma edge_subset (K : Set ℝ²) (t : ℝ) : edge K t ⊆ K := inter_subset_left

lemma eq_of_mem_edge {p : ℝ²} {t : ℝ} (hp : p ∈ edge K t) :
    p = supportFn K t • u t + ⟪p, v t⟫ • v t := by
  conv_lhs => rw [decomp_u_v t p]
  rw [hp.2]

lemma inner_v_le_edgeMax (hK : IsCompact K) {p : ℝ²} {t : ℝ} (hp : p ∈ edge K t) :
    ⟪p, v t⟫ ≤ edgeMax K t := by
  have := le_supportFn (isCompact_edge hK t) hp (t + π / 2)
  rwa [u_add_pi_div_two] at this

lemma edgeMin_le_inner_v (hK : IsCompact K) {p : ℝ²} {t : ℝ} (hp : p ∈ edge K t) :
    edgeMin K t ≤ ⟪p, v t⟫ := by
  have := le_supportFn (isCompact_edge hK t) hp (t + π / 2 + π)
  rw [u_add_pi_div_two_add_pi, inner_neg_right] at this
  unfold edgeMin
  linarith

lemma exists_edgeMax (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    ∃ p ∈ edge K t, ⟪p, v t⟫ = edgeMax K t := by
  obtain ⟨p, hp, h⟩ :=
    exists_supportFn_eq (isCompact_edge hK t) (edge_nonempty hK hne t) (t + π / 2)
  rw [u_add_pi_div_two] at h
  exact ⟨p, hp, h⟩

lemma exists_edgeMin (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    ∃ p ∈ edge K t, ⟪p, v t⟫ = edgeMin K t := by
  obtain ⟨p, hp, h⟩ :=
    exists_supportFn_eq (isCompact_edge hK t) (edge_nonempty hK hne t) (t + π / 2 + π)
  rw [u_add_pi_div_two_add_pi, inner_neg_right] at h
  refine ⟨p, hp, ?_⟩
  unfold edgeMin
  linarith

lemma inner_vtxP_u (K : Set ℝ²) (t : ℝ) : ⟪vtxP K t, u t⟫ = supportFn K t :=
  inner_add_smul_u_v _ _ _

lemma inner_vtxP_v (K : Set ℝ²) (t : ℝ) : ⟪vtxP K t, v t⟫ = edgeMax K t :=
  inner_add_smul_v_v _ _ _

lemma inner_vtxM_u (K : Set ℝ²) (t : ℝ) : ⟪vtxM K t, u t⟫ = supportFn K t :=
  inner_add_smul_u_v _ _ _

lemma inner_vtxM_v (K : Set ℝ²) (t : ℝ) : ⟪vtxM K t, v t⟫ = edgeMin K t :=
  inner_add_smul_v_v _ _ _

lemma vtxP_mem_edge (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) : vtxP K t ∈ edge K t := by
  obtain ⟨p, hp, h⟩ := exists_edgeMax hK hne t
  have e := eq_of_mem_edge hp
  rw [h] at e
  rw [vtxP, ← e]
  exact hp

lemma vtxM_mem_edge (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) : vtxM K t ∈ edge K t := by
  obtain ⟨p, hp, h⟩ := exists_edgeMin hK hne t
  have e := eq_of_mem_edge hp
  rw [h] at e
  rw [vtxM, ← e]
  exact hp

lemma vtxP_mem (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) : vtxP K t ∈ K :=
  (vtxP_mem_edge hK hne t).1

lemma vtxM_mem (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) : vtxM K t ∈ K :=
  (vtxM_mem_edge hK hne t).1

lemma edgeMin_le_edgeMax (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    edgeMin K t ≤ edgeMax K t := by
  obtain ⟨p, hp⟩ := edge_nonempty hK hne t
  exact (edgeMin_le_inner_v hK hp).trans (inner_v_le_edgeMax hK hp)

lemma edgeLength_nonneg (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) : 0 ≤ edgeLength K t :=
  sub_nonneg.2 (edgeMin_le_edgeMax hK hne t)

lemma vtxP_sub_vtxM (K : Set ℝ²) (t : ℝ) : vtxP K t - vtxM K t = edgeLength K t • v t := by
  simp only [vtxP, vtxM, edgeLength, sub_smul]
  abel

/-- For a convex body, the edge is the segment between its two vertices. -/
theorem edge_eq_segment (hK : IsCompact K) (hne : K.Nonempty) (hc : Convex ℝ K) (t : ℝ) :
    edge K t = segment ℝ (vtxM K t) (vtxP K t) := by
  apply Subset.antisymm
  · intro p hp
    have h1 := edgeMin_le_inner_v hK hp
    have h2 := inner_v_le_edgeMax hK hp
    have e := eq_of_mem_edge hp
    rcases (edgeMin_le_edgeMax hK hne t).lt_or_eq with hlt | heq
    · refine ⟨(edgeMax K t - ⟪p, v t⟫) / (edgeMax K t - edgeMin K t),
        (⟪p, v t⟫ - edgeMin K t) / (edgeMax K t - edgeMin K t),
        div_nonneg (by linarith) (by linarith), div_nonneg (by linarith) (by linarith), ?_, ?_⟩
      · have : edgeMax K t - edgeMin K t ≠ 0 := by linarith
        field_simp
        ring
      · have hne' : edgeMax K t - edgeMin K t ≠ 0 := by linarith
        have hθ : (edgeMax K t - ⟪p, v t⟫) / (edgeMax K t - edgeMin K t) * edgeMin K t +
            (⟪p, v t⟫ - edgeMin K t) / (edgeMax K t - edgeMin K t) * edgeMax K t = ⟪p, v t⟫ := by
          field_simp
          ring
        have hs : (edgeMax K t - ⟪p, v t⟫) / (edgeMax K t - edgeMin K t) +
            (⟪p, v t⟫ - edgeMin K t) / (edgeMax K t - edgeMin K t) = 1 := by
          field_simp
          ring
        calc ((edgeMax K t - ⟪p, v t⟫) / (edgeMax K t - edgeMin K t)) • vtxM K t +
              ((⟪p, v t⟫ - edgeMin K t) / (edgeMax K t - edgeMin K t)) • vtxP K t
            = ((edgeMax K t - ⟪p, v t⟫) / (edgeMax K t - edgeMin K t) +
                (⟪p, v t⟫ - edgeMin K t) / (edgeMax K t - edgeMin K t)) • (supportFn K t • u t) +
              ((edgeMax K t - ⟪p, v t⟫) / (edgeMax K t - edgeMin K t) * edgeMin K t +
                (⟪p, v t⟫ - edgeMin K t) / (edgeMax K t - edgeMin K t) * edgeMax K t) • v t := by
              simp only [vtxP, vtxM]
              module
          _ = p := by rw [hs, hθ, one_smul, ← e]
    · have hp' : p = vtxP K t := by
        rw [e, vtxP]
        congr 2
        linarith
      rw [hp']
      exact right_mem_segment _ _ _
  · exact (convex_edge hc t).segment_subset (vtxM_mem_edge hK hne t) (vtxP_mem_edge hK hne t)

/-! ## Monotonicity of edges -/

/-- For `0 < s - t ≤ π/2`, the edge `e_K(s)` lies beyond `e_K(t)` in the direction `v_t`. -/
lemma inner_v_le_of_mem_edge (hK : IsCompact K) {t s : ℝ} (hts : t < s) (hst : s ≤ t + π / 2)
    {a p : ℝ²} (ha : a ∈ edge K t) (hp : p ∈ edge K s) : ⟪a, v t⟫ ≤ ⟪p, v t⟫ := by
  have h1 : ⟪a, u s⟫ ≤ ⟪p, u s⟫ := by rw [hp.2]; exact le_supportFn hK ha.1 s
  have h2 : ⟪p, u t⟫ ≤ ⟪a, u t⟫ := by rw [ha.2]; exact le_supportFn hK hp.1 t
  rw [inner_u_decomp' a s t, inner_u_decomp' p s t] at h1
  have hsin : 0 < sin (s - t) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have hcos : 0 ≤ cos (s - t) := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith⟩
  nlinarith [mul_nonneg hcos (sub_nonneg.2 h2)]

/-- For `0 < s - t ≤ π/2`, the edge `e_K(t)` lies before `e_K(s)` in the direction `v_s`. -/
lemma inner_v_le_of_mem_edge' (hK : IsCompact K) {t s : ℝ} (hts : t < s) (hst : s ≤ t + π / 2)
    {a p : ℝ²} (ha : a ∈ edge K t) (hp : p ∈ edge K s) : ⟪a, v s⟫ ≤ ⟪p, v s⟫ := by
  have h1 : ⟪a, u s⟫ ≤ ⟪p, u s⟫ := by rw [hp.2]; exact le_supportFn hK ha.1 s
  have h2 : ⟪p, u t⟫ ≤ ⟪a, u t⟫ := by rw [ha.2]; exact le_supportFn hK hp.1 t
  rw [inner_u_decomp' a t s, inner_u_decomp' p t s] at h2
  have hsin : sin (t - s) < 0 := by
    rw [← neg_sub, sin_neg]
    exact neg_neg_of_pos (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos]))
  have hcos : 0 ≤ cos (t - s) := cos_nonneg_of_mem_Icc ⟨by linarith, by linarith [pi_pos]⟩
  nlinarith [mul_nonneg hcos (sub_nonneg.2 h1)]

/-! ## Theorem 2.1.3 -/

/-- As `s → t⁺`, the edges `e_K(s)` shrink to the vertex `v⁺_K(t)`. -/
lemma eventually_edge_subset_ball_right (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ s in 𝓝[>] t, ∀ p ∈ edge K s, dist p (vtxP K t) < ε := by
  have h1 : ∀ᶠ s in 𝓝 t, edge K s ⊆ Metric.thickening (ε / 2) (edge K t) :=
    (isOpen_setOf_edge_subset hK hne Metric.isOpen_thickening).mem_nhds
      (Metric.self_subset_thickening (by positivity) _)
  filter_upwards [nhdsWithin_le_nhds h1, Ioo_mem_nhdsGT (by linarith [pi_pos] : t < t + π / 2)]
    with s hs1 hs2 p hp
  obtain ⟨q, hq, hpq⟩ := Metric.mem_thickening_iff.1 (hs1 hp)
  have hkey := inner_v_le_of_mem_edge hK hs2.1 hs2.2.le (vtxP_mem_edge hK hne t) hp
  rw [inner_vtxP_v] at hkey
  have hqv := inner_v_le_edgeMax hK hq
  have hdq : dist q (vtxP K t) = edgeMax K t - ⟪q, v t⟫ := by
    rw [dist_eq_norm, eq_of_mem_edge hq, vtxP, inner_add_smul_v_v]
    rw [show supportFn K t • u t + ⟪q, v t⟫ • v t - (supportFn K t • u t + edgeMax K t • v t) =
      (⟪q, v t⟫ - edgeMax K t) • v t by module]
    rw [norm_smul, norm_v, mul_one, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hpq' : ⟪p, v t⟫ - ⟪q, v t⟫ ≤ dist p q := by
    rw [← inner_sub_left, dist_eq_norm]
    calc ⟪p - q, v t⟫ ≤ ‖p - q‖ * ‖v t‖ := real_inner_le_norm _ _
      _ = ‖p - q‖ := by rw [norm_v, mul_one]
  calc dist p (vtxP K t) ≤ dist p q + dist q (vtxP K t) := dist_triangle _ _ _
    _ < ε := by rw [hdq]; linarith

/-- As `s → t⁻`, the edges `e_K(s)` shrink to the vertex `v⁻_K(t)`. -/
lemma eventually_edge_subset_ball_left (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ s in 𝓝[<] t, ∀ p ∈ edge K s, dist p (vtxM K t) < ε := by
  have h1 : ∀ᶠ s in 𝓝 t, edge K s ⊆ Metric.thickening (ε / 2) (edge K t) :=
    (isOpen_setOf_edge_subset hK hne Metric.isOpen_thickening).mem_nhds
      (Metric.self_subset_thickening (by positivity) _)
  filter_upwards [nhdsWithin_le_nhds h1, Ioo_mem_nhdsLT (by linarith [pi_pos] : t - π / 2 < t)]
    with s hs1 hs2 p hp
  obtain ⟨q, hq, hpq⟩ := Metric.mem_thickening_iff.1 (hs1 hp)
  have hkey := inner_v_le_of_mem_edge' hK hs2.2 (by linarith [hs2.1]) hp (vtxM_mem_edge hK hne t)
  rw [inner_vtxM_v] at hkey
  have hqv := edgeMin_le_inner_v hK hq
  have hdq : dist q (vtxM K t) = ⟪q, v t⟫ - edgeMin K t := by
    rw [dist_eq_norm, eq_of_mem_edge hq, vtxM, inner_add_smul_v_v]
    rw [show supportFn K t • u t + ⟪q, v t⟫ • v t - (supportFn K t • u t + edgeMin K t • v t) =
      (⟪q, v t⟫ - edgeMin K t) • v t by module]
    rw [norm_smul, norm_v, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hpq' : ⟪q, v t⟫ - ⟪p, v t⟫ ≤ dist p q := by
    rw [← inner_sub_left, dist_comm, dist_eq_norm]
    calc ⟪q - p, v t⟫ ≤ ‖q - p‖ * ‖v t‖ := real_inner_le_norm _ _
      _ = ‖q - p‖ := by rw [norm_v, mul_one]
  calc dist p (vtxM K t) ≤ dist p q + dist q (vtxM K t) := dist_triangle _ _ _
    _ < ε := by rw [hdq]; linarith

lemma tendsto_of_mem_edge_right (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) {f : ℝ → ℝ²}
    (hf : ∀ᶠ s in 𝓝[>] t, f s ∈ edge K s) : Tendsto f (𝓝[>] t) (𝓝 (vtxP K t)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hf, eventually_edge_subset_ball_right hK hne t hε] with s h1 h2
  exact h2 _ h1

lemma tendsto_of_mem_edge_left (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) {f : ℝ → ℝ²}
    (hf : ∀ᶠ s in 𝓝[<] t, f s ∈ edge K s) : Tendsto f (𝓝[<] t) (𝓝 (vtxM K t)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hf, eventually_edge_subset_ball_left hK hne t hε] with s h1 h2
  exact h2 _ h1

/-- **Thm 2.1.3** (right limit of `v⁺`): `v⁺_K` is right-continuous. -/
theorem tendsto_vtxP_right (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    Tendsto (vtxP K) (𝓝[>] t) (𝓝 (vtxP K t)) :=
  tendsto_of_mem_edge_right hK hne t (Eventually.of_forall fun s => vtxP_mem_edge hK hne s)

/-- **Thm 2.1.3** (right limit of `v⁻`). -/
theorem tendsto_vtxM_right (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    Tendsto (vtxM K) (𝓝[>] t) (𝓝 (vtxP K t)) :=
  tendsto_of_mem_edge_right hK hne t (Eventually.of_forall fun s => vtxM_mem_edge hK hne s)

/-- **Thm 2.1.3** (left limit of `v⁺`). -/
theorem tendsto_vtxP_left (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    Tendsto (vtxP K) (𝓝[<] t) (𝓝 (vtxM K t)) :=
  tendsto_of_mem_edge_left hK hne t (Eventually.of_forall fun s => vtxP_mem_edge hK hne s)

/-- **Thm 2.1.3** (left limit of `v⁻`): `v⁻_K` is left-continuous. -/
theorem tendsto_vtxM_left (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    Tendsto (vtxM K) (𝓝[<] t) (𝓝 (vtxM K t)) :=
  tendsto_of_mem_edge_left hK hne t (Eventually.of_forall fun s => vtxM_mem_edge hK hne s)

theorem continuousWithinAt_vtxP (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    ContinuousWithinAt (vtxP K) (Ici t) t := by
  rw [continuousWithinAt_Ioi_iff_Ici.symm]
  exact tendsto_vtxP_right hK hne t

theorem continuousWithinAt_vtxM (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    ContinuousWithinAt (vtxM K) (Iic t) t := by
  rw [continuousWithinAt_Iio_iff_Iic.symm]
  exact tendsto_vtxM_left hK hne t

/-! ## One-sided derivatives of the support function -/

lemma hasDerivAt_inner_u (a : ℝ²) (t : ℝ) : HasDerivAt (fun s => ⟪a, u s⟫) ⟪a, v t⟫ t := by
  have h1 : HasDerivAt (fun s => a 0 * cos s + a 1 * sin s) (a 0 * -sin t + a 1 * cos t) t :=
    ((hasDerivAt_cos t).const_mul (a 0)).add ((hasDerivAt_sin t).const_mul (a 1))
  have e1 : (fun s => ⟪a, u s⟫) = fun s => a 0 * cos s + a 1 * sin s := by
    funext s; rw [inner_eq, u_coord_zero, u_coord_one]
  have e2 : ⟪a, v t⟫ = a 0 * -sin t + a 1 * cos t := by
    rw [inner_eq, v_coord_zero, v_coord_one]
  rw [e1, e2]
  exact h1

lemma tendsto_slope_right_of_hasDerivAt {f : ℝ → ℝ} {f' t : ℝ} (h : HasDerivAt f f' t) :
    Tendsto (slope f t) (𝓝[>] t) (𝓝 f') :=
  (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).1 h.hasDerivWithinAt

lemma tendsto_slope_left_of_hasDerivAt {f : ℝ → ℝ} {f' t : ℝ} (h : HasDerivAt f f' t) :
    Tendsto (slope f t) (𝓝[<] t) (𝓝 f') :=
  (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).1 h.hasDerivWithinAt

lemma hasDerivAt_cos_sub (t : ℝ) : HasDerivAt (fun s => cos (s - t)) 0 t := by
  simpa using ((hasDerivAt_id t).sub_const t).cos

lemma hasDerivAt_sin_sub (t : ℝ) : HasDerivAt (fun s => sin (s - t)) 1 t := by
  simpa using ((hasDerivAt_id t).sub_const t).sin

/-- The auxiliary quotient `(h(t)(cos(s-t) - 1) + ⟪w(s), v_t⟫ sin(s-t)) / (s - t)` tends to
`lim ⟪w(s), v_t⟫`. -/
lemma tendsto_aux_quot {t : ℝ} {F : Filter ℝ} (hF : F ≤ 𝓝[≠] t) (c : ℝ) {w : ℝ → ℝ²} {m : ℝ}
    (hw : Tendsto (fun s => ⟪w s, v t⟫) F (𝓝 m)) :
    Tendsto (fun s => (c * (cos (s - t) - 1) + ⟪w s, v t⟫ * sin (s - t)) / (s - t)) F (𝓝 m) := by
  have hc : Tendsto (slope (fun s => cos (s - t)) t) F (𝓝 0) :=
    ((hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_cos_sub t))).mono_left hF
  have hs : Tendsto (slope (fun s => sin (s - t)) t) F (𝓝 1) :=
    ((hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_sin_sub t))).mono_left hF
  have h := (tendsto_const_nhds (x := c)).mul hc |>.add (hw.mul hs)
  rw [mul_zero, zero_add, mul_one] at h
  refine h.congr' ?_
  filter_upwards [hF self_mem_nhdsWithin] with s hs
  simp only [slope_def_field, sub_self, cos_zero, sin_zero, sub_zero]
  ring

/-- The right derivative of the support function is `⟪v⁺_K(t), v_t⟫`. -/
theorem hasDerivWithinAt_supportFn_Ioi (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    HasDerivWithinAt (supportFn K) (edgeMax K t) (Ioi t) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi]
  have hg := hasDerivAt_inner_u (vtxP K t) t
  rw [inner_vtxP_v] at hg
  have hlow := tendsto_slope_right_of_hasDerivAt hg
  have hw : Tendsto (fun s => ⟪vtxP K s, v t⟫) (𝓝[>] t) (𝓝 (edgeMax K t)) := by
    have := (tendsto_vtxP_right hK hne t).inner (𝕜 := ℝ) (tendsto_const_nhds (x := v t))
    rwa [inner_vtxP_v] at this
  have hup := tendsto_aux_quot (nhdsWithin_mono t (fun s (hs : t < s) => hs.ne')) (supportFn K t) hw
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s (hs : t < s)
    rw [slope_def_field, slope_def_field]
    have h1 : ⟪vtxP K t, u s⟫ ≤ supportFn K s := le_supportFn hK (vtxP_mem hK hne t) s
    rw [inner_vtxP_u]
    exact div_le_div_of_nonneg_right (by linarith) (sub_pos.2 hs).le
  · filter_upwards [Ioo_mem_nhdsGT (by linarith [pi_pos] : t < t + π / 2)] with s hs
    rw [slope_def_field]
    have hst : 0 < s - t := sub_pos.2 hs.1
    have hcos : 0 ≤ cos (s - t) :=
      cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith [hs.2]⟩
    have hp := vtxP_mem_edge hK hne s
    have e1 : supportFn K s =
        ⟪vtxP K s, u t⟫ * cos (s - t) + ⟪vtxP K s, v t⟫ * sin (s - t) := by
      rw [← inner_u_decomp', inner_vtxP_u]
    have e2 : ⟪vtxP K s, u t⟫ ≤ supportFn K t := le_supportFn hK hp.1 t
    apply div_le_div_of_nonneg_right _ hst.le
    rw [e1]
    nlinarith [mul_le_mul_of_nonneg_right e2 hcos]

/-- The left derivative of the support function is `⟪v⁻_K(t), v_t⟫`. -/
theorem hasDerivWithinAt_supportFn_Iio (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    HasDerivWithinAt (supportFn K) (edgeMin K t) (Iio t) t := by
  rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio]
  have hg := hasDerivAt_inner_u (vtxM K t) t
  rw [inner_vtxM_v] at hg
  have hup := tendsto_slope_left_of_hasDerivAt hg
  have hw : Tendsto (fun s => ⟪vtxM K s, v t⟫) (𝓝[<] t) (𝓝 (edgeMin K t)) := by
    have := (tendsto_vtxM_left hK hne t).inner (𝕜 := ℝ) (tendsto_const_nhds (x := v t))
    rwa [inner_vtxM_v] at this
  have hlow := tendsto_aux_quot (nhdsWithin_mono t (fun s (hs : s < t) => hs.ne)) (supportFn K t) hw
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [Ioo_mem_nhdsLT (by linarith [pi_pos] : t - π / 2 < t)] with s hs
    rw [slope_def_field]
    have hst : s - t < 0 := sub_neg.2 hs.2
    have hcos : 0 ≤ cos (s - t) :=
      cos_nonneg_of_mem_Icc ⟨by linarith [hs.1], by linarith [pi_pos]⟩
    have hp := vtxM_mem_edge hK hne s
    have e1 : supportFn K s =
        ⟪vtxM K s, u t⟫ * cos (s - t) + ⟪vtxM K s, v t⟫ * sin (s - t) := by
      rw [← inner_u_decomp', inner_vtxM_u]
    have e2 : ⟪vtxM K s, u t⟫ ≤ supportFn K t := le_supportFn hK hp.1 t
    apply div_le_div_of_nonpos_of_le hst.le
    rw [e1]
    nlinarith [mul_le_mul_of_nonneg_right e2 hcos]
  · filter_upwards [self_mem_nhdsWithin] with s (hs : s < t)
    rw [slope_def_field, slope_def_field]
    have h1 : ⟪vtxM K t, u s⟫ ≤ supportFn K s := le_supportFn hK (vtxM_mem hK hne t) s
    rw [inner_vtxM_u]
    exact div_le_div_of_nonpos_of_le (sub_neg.2 hs).le (by linarith)

/-! ## The vertex `v_K(t, s)` (Def 2.1.14) -/

lemma inner_vtx2_u_left (K : Set ℝ²) (a b : ℝ) : ⟪vtx2 K a b, u a⟫ = supportFn K a :=
  inner_add_smul_u_v _ _ _

lemma inner_vtx2_u_right (K : Set ℝ²) {a b : ℝ} (hab : sin (b - a) ≠ 0) :
    ⟪vtx2 K a b, u b⟫ = supportFn K b := by
  rw [inner_u_decomp' _ b a, vtx2, inner_add_smul_u_v, inner_add_smul_v_v]
  field_simp
  ring

/-- **Thm 2.1.3** (right limit of `v_K(t, s)`). -/
theorem tendsto_vtx2_right (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    Tendsto (vtx2 K t) (𝓝[>] t) (𝓝 (vtxP K t)) := by
  have hd := hasDerivWithinAt_supportFn_Ioi hK hne t
  rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi] at hd
  -- the coefficient `(h(s) - h(t) cos (s-t)) / sin (s-t)` tends to `m⁺`
  have hcoef : Tendsto (fun s => (supportFn K s - supportFn K t * cos (s - t)) / sin (s - t))
      (𝓝[>] t) (𝓝 (edgeMax K t)) := by
    -- write it as `(slope h + h(t) · (1 - cos)/(s-t)) / (sin (s-t) / (s-t))`
    have hc : Tendsto (slope (fun s => cos (s - t)) t) (𝓝[>] t) (𝓝 0) :=
      tendsto_slope_right_of_hasDerivAt (hasDerivAt_cos_sub t)
    have hs : Tendsto (slope (fun s => sin (s - t)) t) (𝓝[>] t) (𝓝 1) :=
      tendsto_slope_right_of_hasDerivAt (hasDerivAt_sin_sub t)
    have h := (hd.sub ((tendsto_const_nhds (x := supportFn K t)).mul hc)).div hs one_ne_zero
    rw [mul_zero, sub_zero, div_one] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by linarith [pi_pos] : t < t + π)] with s hs
    have hst : s - t ≠ 0 := (sub_pos.2 hs.1).ne'
    have hsin : sin (s - t) ≠ 0 :=
      (sin_pos_of_pos_of_lt_pi (sub_pos.2 hs.1) (by linarith [hs.2])).ne'
    simp only [Pi.div_apply, slope_def_field, sub_self, cos_zero, sin_zero, sub_zero]
    field_simp
    ring
  have h := ((tendsto_const_nhds (x := supportFn K t • u t)).add
    (hcoef.smul (tendsto_const_nhds (x := v t))))
  exact h

/-- **Thm 2.1.3** (left limit of `v_K(s, t)`). -/
theorem tendsto_vtx2_left (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    Tendsto (fun s => vtx2 K s t) (𝓝[<] t) (𝓝 (vtxM K t)) := by
  have hd := hasDerivWithinAt_supportFn_Iio hK hne t
  rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio] at hd
  -- `v_K(s, t) = h(t) u_t + ((h(t) cos (t-s) - h(s)) / sin (t-s)) v_t`
  have hcoef : Tendsto (fun s => (supportFn K s - supportFn K t * cos (s - t)) / sin (s - t))
      (𝓝[<] t) (𝓝 (edgeMin K t)) := by
    have hc : Tendsto (slope (fun s => cos (s - t)) t) (𝓝[<] t) (𝓝 0) :=
      tendsto_slope_left_of_hasDerivAt (hasDerivAt_cos_sub t)
    have hs : Tendsto (slope (fun s => sin (s - t)) t) (𝓝[<] t) (𝓝 1) :=
      tendsto_slope_left_of_hasDerivAt (hasDerivAt_sin_sub t)
    have h := (hd.sub ((tendsto_const_nhds (x := supportFn K t)).mul hc)).div hs one_ne_zero
    rw [mul_zero, sub_zero, div_one] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (by linarith [pi_pos] : t - π < t)] with s hs
    have hst : s - t ≠ 0 := (sub_neg.2 hs.2).ne
    have hsin : sin (s - t) ≠ 0 := by
      rw [← neg_sub, sin_neg, neg_ne_zero]
      exact (sin_pos_of_pos_of_lt_pi (sub_pos.2 hs.2) (by linarith [hs.1])).ne'
    simp only [Pi.div_apply, slope_def_field, sub_self, cos_zero, sin_zero, sub_zero]
    field_simp
    ring
  have hlim := ((tendsto_const_nhds (x := supportFn K t • u t)).add
    (hcoef.smul (tendsto_const_nhds (x := v t))))
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by linarith [pi_pos] : t - π < t)] with s hs
  -- both sides are the intersection point of `l_K(s)` and `l_K(t)`
  have hsin : sin (t - s) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (sub_pos.2 hs.2) (by linarith [hs.1])).ne'
  have hsin' : sin (s - t) ≠ 0 := by
    rw [← neg_sub, sin_neg, neg_ne_zero]; exact hsin
  apply eq_of_inner_u_v_eq (t := t)
  · rw [inner_add_smul_u_v, inner_vtx2_u_right K hsin]
  · rw [inner_add_smul_v_v, vtx2, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_u_v_eq_sin, inner_v_v_eq_cos]
    rw [show s - t = -(t - s) by ring, sin_neg, cos_neg] at *
    field_simp
    linear_combination (supportFn K s) * sin_sq_add_cos_sq (t - s)

end Sofa
