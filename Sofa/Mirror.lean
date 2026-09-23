/-
# Sofa/Mirror.lean — the mirror symmetry `M_ω` (Baek Def 2.5.6, Prop 2.5.4, Remark 2.5.1)

`M_ω` is the reflection in the line through `O` and `o_ω` (direction angle `ω/2 + π/4`).  It
satisfies `⟪M_ω p, u_t⟫ = ⟪p, u_{ω+π/2-t}⟫` and `⟪M_ω p, v_t⟫ = -⟪p, v_{ω+π/2-t}⟫`, hence
`h_{M_ω K}(t) = h_K(ω + π/2 - t)`.  We transport: caps, niches, edges, vertices, corners, volume.

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 1 (2026-09-17, Opus 5): compiled in the cloud dev tree
(Lean 4.33.1, Mathlib v4.33.1 with subset imports), no `sorry`; full `import Mathlib` re-check pending.
-/
import Sofa.Vertex

noncomputable section

open Real Set MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²} {ω : ℝ}

/-- **Def 2.5.6.** The reflection `M_ω`. -/
def mirror (ω : ℝ) (p : ℝ²) : ℝ² :=
  !₂[p 0 * cos (ω + π / 2) + p 1 * sin (ω + π / 2),
    p 0 * sin (ω + π / 2) - p 1 * cos (ω + π / 2)]

@[simp] lemma mirror_coord_zero (ω : ℝ) (p : ℝ²) :
    mirror ω p 0 = p 0 * cos (ω + π / 2) + p 1 * sin (ω + π / 2) := rfl

@[simp] lemma mirror_coord_one (ω : ℝ) (p : ℝ²) :
    mirror ω p 1 = p 0 * sin (ω + π / 2) - p 1 * cos (ω + π / 2) := rfl

lemma inner_mirror_u (ω t : ℝ) (p : ℝ²) : ⟪mirror ω p, u t⟫ = ⟪p, u (ω + π / 2 - t)⟫ := by
  simp only [inner_eq, mirror_coord_zero, mirror_coord_one, u_coord_zero, u_coord_one,
    cos_sub, sin_sub]
  ring

lemma inner_mirror_v (ω t : ℝ) (p : ℝ²) : ⟪mirror ω p, v t⟫ = -⟪p, v (ω + π / 2 - t)⟫ := by
  simp only [inner_eq, mirror_coord_zero, mirror_coord_one, v_coord_zero, v_coord_one,
    cos_sub, sin_sub]
  ring

lemma mirror_mirror (ω : ℝ) (p : ℝ²) : mirror ω (mirror ω p) = p := by
  apply eq_of_inner_u_v_eq (t := 0)
  · rw [inner_mirror_u, inner_mirror_u]
    congr 2
    ring
  · rw [inner_mirror_v, inner_mirror_v, neg_neg]
    congr 2
    ring

lemma mirror_involutive (ω : ℝ) : Function.Involutive (mirror ω) := mirror_mirror ω

lemma mirror_add (ω : ℝ) (p q : ℝ²) : mirror ω (p + q) = mirror ω p + mirror ω q := by
  apply eq_of_inner_u_v_eq (t := 0)
  · rw [inner_add_left, inner_mirror_u, inner_mirror_u, inner_mirror_u, inner_add_left]
  · rw [inner_add_left, inner_mirror_v, inner_mirror_v, inner_mirror_v, inner_add_left]
    ring

lemma mirror_smul (ω c : ℝ) (p : ℝ²) : mirror ω (c • p) = c • mirror ω p := by
  apply eq_of_inner_u_v_eq (t := 0)
  · rw [real_inner_smul_left, inner_mirror_u, inner_mirror_u, real_inner_smul_left]
  · rw [real_inner_smul_left, inner_mirror_v, inner_mirror_v, real_inner_smul_left]
    ring

lemma inner_mirror_mirror (ω : ℝ) (p q : ℝ²) : ⟪mirror ω p, mirror ω q⟫ = ⟪p, q⟫ := by
  simp only [inner_eq, mirror_coord_zero, mirror_coord_one]
  linear_combination (p 0 * q 0 + p 1 * q 1) * sin_sq_add_cos_sq (ω + π / 2)

/-- `M_ω` as a linear isometric equivalence. -/
def mirrorL (ω : ℝ) : ℝ² ≃ₗᵢ[ℝ] ℝ² :=
  LinearEquiv.isometryOfInner
    (LinearEquiv.ofInvolutive
      { toFun := mirror ω, map_add' := mirror_add ω, map_smul' := mirror_smul ω }
      (mirror_involutive ω))
    (inner_mirror_mirror ω)

@[simp] lemma coe_mirrorL (ω : ℝ) : ⇑(mirrorL ω) = mirror ω := rfl

lemma continuous_mirror (ω : ℝ) : Continuous (mirror ω) := (mirrorL ω).continuous

lemma mirror_image_eq_preimage (ω : ℝ) (S : Set ℝ²) : mirror ω '' S = mirror ω ⁻¹' S :=
  congrFun (image_eq_preimage_of_inverse (mirror_involutive ω) (mirror_involutive ω)) S

lemma mem_mirror_image {S : Set ℝ²} {p : ℝ²} : p ∈ mirror ω '' S ↔ mirror ω p ∈ S := by
  rw [mirror_image_eq_preimage]; rfl

lemma mirror_image_mirror_image (ω : ℝ) (S : Set ℝ²) : mirror ω '' (mirror ω '' S) = S := by
  ext p; rw [mem_mirror_image, mem_mirror_image, mirror_mirror]

lemma volume_mirror_image (ω : ℝ) (S : Set ℝ²) : volume (mirror ω '' S) = volume S := by
  rw [mirror_image_eq_preimage, ← coe_mirrorL]
  exact (mirrorL ω).measurePreserving.measure_preimage_emb
    (mirrorL ω).toHomeomorph.measurableEmbedding S

lemma isCompact_mirror_image {S : Set ℝ²} (hS : IsCompact S) (ω : ℝ) :
    IsCompact (mirror ω '' S) := hS.image (continuous_mirror ω)

lemma convex_mirror_image {S : Set ℝ²} (hS : Convex ℝ S) (ω : ℝ) :
    Convex ℝ (mirror ω '' S) := by
  have := hS.linear_image (mirrorL ω).toLinearEquiv.toLinearMap
  exact this

lemma isConnected_mirror_image {S : Set ℝ²} (hS : IsConnected S) (ω : ℝ) :
    IsConnected (mirror ω '' S) := hS.image _ (continuous_mirror ω).continuousOn

lemma isClosed_mirror_image {S : Set ℝ²} (hS : IsClosed S) (ω : ℝ) :
    IsClosed (mirror ω '' S) := by
  rw [mirror_image_eq_preimage]; exact hS.preimage (continuous_mirror ω)

/-! ## Support functions and the standard sets -/

lemma supportFn_mirror (ω : ℝ) (S : Set ℝ²) (t : ℝ) :
    supportFn (mirror ω '' S) t = supportFn S (ω + π / 2 - t) := by
  unfold supportFn
  rw [image_image]
  have : (fun x => proj t (mirror ω x)) = proj (ω + π / 2 - t) := by
    funext x; exact inner_mirror_u ω t x
  rw [this]

lemma mem_fan_mirror {p : ℝ²} : mirror ω p ∈ fan ω ↔ p ∈ fan ω := by
  have h1 : mirror ω p 1 = ⟪p, u ω⟫ := by
    rw [← inner_u_pi_div_two, inner_mirror_u]; congr 2; ring
  have h2 : ⟪mirror ω p, u ω⟫ = p 1 := by
    rw [inner_mirror_u, ← inner_u_pi_div_two]; congr 2; ring
  simp only [fan, mem_ofPred_eq, h1, h2]
  exact and_comm

lemma mem_para_mirror {p : ℝ²} : mirror ω p ∈ para ω ↔ p ∈ para ω := by
  have h1 : mirror ω p 1 = ⟪p, u ω⟫ := by
    rw [← inner_u_pi_div_two, inner_mirror_u]; congr 2; ring
  have h2 : ⟪mirror ω p, u ω⟫ = p 1 := by
    rw [inner_mirror_u, ← inner_u_pi_div_two]; congr 2; ring
  simp only [para, Hstrip, Vstrip, mem_inter_iff, mem_ofPred_eq, h1, h2]
  exact and_comm

lemma mirror_image_fan (ω : ℝ) : mirror ω '' fan ω = fan ω := by
  ext p; rw [mem_mirror_image, mem_fan_mirror]

lemma mirror_image_para (ω : ℝ) : mirror ω '' para ω = para ω := by
  ext p; rw [mem_mirror_image, mem_para_mirror]

lemma mirror_mem_QminusS_iff (S : Set ℝ²) {t : ℝ} {p : ℝ²} :
    mirror ω p ∈ QminusS (mirror ω '' S) t ↔ p ∈ QminusS S (ω - t) := by
  rw [mem_QminusS_iff, mem_QminusS_iff, inner_mirror_u, inner_mirror_u, supportFn_mirror,
    supportFn_mirror]
  rw [show ω + π / 2 - (t + π / 2) = ω - t by ring, show ω - t + π / 2 = ω + π / 2 - t by ring]
  exact and_comm

lemma mirror_mem_QplusS_iff (S : Set ℝ²) {t : ℝ} {p : ℝ²} :
    mirror ω p ∈ QplusS (mirror ω '' S) t ↔ p ∈ QplusS S (ω - t) := by
  rw [mem_QplusS_iff, mem_QplusS_iff, inner_mirror_u, inner_mirror_u, supportFn_mirror,
    supportFn_mirror]
  rw [show ω + π / 2 - (t + π / 2) = ω - t by ring, show ω - t + π / 2 = ω + π / 2 - t by ring]
  exact and_comm

/-- **Prop 2.5.4** (niche): `N(M_ω K) = M_ω N(K)`. -/
theorem niche_mirror (K : Set ℝ²) (ω : ℝ) : niche (mirror ω '' K) ω = mirror ω '' niche K ω := by
  ext p
  rw [mem_mirror_image, mem_niche_iff, mem_niche_iff, ← mirror_mirror ω p, mirror_mirror,
    mem_fan_mirror]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨t, ht, hQ⟩
    rw [← mirror_mirror ω p, mirror_mem_QminusS_iff] at hQ
    exact ⟨ω - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, hQ⟩
  · rintro ⟨t, ht, hQ⟩
    refine ⟨ω - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    rw [← mirror_mirror ω p, mirror_mem_QminusS_iff, sub_sub_cancel]
    exact hQ

/-! ## Caps -/

lemma capAngles_reflect {t : ℝ} (ht : t ∈ capAngles ω) :
    ∃ s ∈ capAngles ω, s = ω + π / 2 - t ∨ s = ω + π / 2 - t + 2 * π := by
  rcases ht with (ht | ht) | ht | ht
  · exact ⟨_, Or.inl (Or.inr ⟨by linarith [ht.2], by linarith [ht.1]⟩), Or.inl rfl⟩
  · exact ⟨_, Or.inl (Or.inl ⟨by linarith [ht.2], by linarith [ht.1]⟩), Or.inl rfl⟩
  · refine ⟨3 * π / 2, Or.inr (Or.inr rfl), Or.inr ?_⟩
    rw [ht]; ring
  · rw [mem_singleton_iff] at ht
    refine ⟨ω + π, Or.inr (Or.inl rfl), Or.inr ?_⟩
    rw [ht]; ring

lemma u_supportFn_of_reflect {S : Set ℝ²} {t s : ℝ}
    (h : s = ω + π / 2 - t ∨ s = ω + π / 2 - t + 2 * π) :
    u s = u (ω + π / 2 - t) ∧ supportFn S s = supportFn S (ω + π / 2 - t) := by
  rcases h with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · exact ⟨u_add_two_pi _, supportFn_add_two_pi _ _⟩

/-- **Prop 2.5.4** (caps): the mirror image of a cap is a cap. -/
theorem IsCap.image_mirror (hK : IsCap K ω) : IsCap (mirror ω '' K) ω := by
  have hper : ∀ x, supportFn K (x + 2 * π) = supportFn K x := supportFn_add_two_pi K
  refine ⟨convex_mirror_image hK.convex ω, isCompact_mirror_image hK.isCompact ω,
    hK.nonempty.image _, ?_, ?_, ?_, ?_, ?_⟩
  · rw [supportFn_mirror, show ω + π / 2 - ω = π / 2 by ring, hK.supportFn_pi_div_two]
  · rw [supportFn_mirror, show ω + π / 2 - π / 2 = ω by ring, hK.supportFn_ω]
  · rw [supportFn_mirror, show ω + π / 2 - (ω + π) = 3 * π / 2 - 2 * π by ring, ← hper,
      sub_add_cancel, hK.supportFn_three_pi_div_two]
  · rw [supportFn_mirror, show ω + π / 2 - 3 * π / 2 = ω + π - 2 * π by ring, ← hper,
      sub_add_cancel, hK.supportFn_ω_add_pi]
  · ext p
    simp only [mem_iInter₂, hpLe, mem_ofPred_eq, supportFn_mirror]
    rw [mem_mirror_image, hK.mem_iff]
    constructor
    · intro h t ht
      obtain ⟨s, hs, hst⟩ := capAngles_reflect ht
      obtain ⟨-, hh⟩ := u_supportFn_of_reflect (S := K) hst
      have := h s hs
      rw [inner_mirror_u, hh] at this
      have hu : u (ω + π / 2 - s) = u t := by
        rcases hst with h' | h'
        · rw [h']; congr 1; ring
        · rw [h', show ω + π / 2 - (ω + π / 2 - t + 2 * π) = t - 2 * π by ring,
            ← u_add_two_pi, sub_add_cancel]
      rwa [hu] at this
    · intro h s hs
      obtain ⟨t, ht, hts⟩ := capAngles_reflect hs
      have := h t ht
      rw [inner_mirror_u]
      have hu : u (ω + π / 2 - s) = u t := by
        rcases hts with h' | h'
        · rw [h']
        · rw [h', u_add_two_pi]
      have hh' : supportFn K (ω + π / 2 - t) = supportFn K s := by
        rcases hts with h' | h'
        · rw [h']; congr 1; ring
        · rw [h', show ω + π / 2 - (ω + π / 2 - s + 2 * π) = s - 2 * π by ring]
          have := hper (s - 2 * π)
          rw [sub_add_cancel] at this
          exact this.symm
      rw [hu, ← hh']
      exact this

/-! ## Edges and vertices -/

lemma edge_mirror (S : Set ℝ²) (ω t : ℝ) :
    edge (mirror ω '' S) t = mirror ω '' edge S (ω + π / 2 - t) := by
  ext p
  rw [mem_mirror_image]
  simp only [edge, supportLine, line, mem_inter_iff, mem_ofPred_eq, supportFn_mirror]
  rw [mem_mirror_image, ← inner_mirror_u, mirror_mirror]

lemma edgeMax_mirror (S : Set ℝ²) (ω t : ℝ) :
    edgeMax (mirror ω '' S) t = -edgeMin S (ω + π / 2 - t) := by
  unfold edgeMax edgeMin
  rw [edge_mirror, supportFn_mirror, neg_neg,
    show ω + π / 2 - t + π / 2 + π = ω + π / 2 - (t + π / 2) + 2 * π by ring,
    supportFn_add_two_pi]

lemma edgeMin_mirror (S : Set ℝ²) (ω t : ℝ) :
    edgeMin (mirror ω '' S) t = -edgeMax S (ω + π / 2 - t) := by
  unfold edgeMax edgeMin
  rw [edge_mirror, supportFn_mirror,
    show ω + π / 2 - t + π / 2 = ω + π / 2 - (t + π / 2 + π) + 2 * π by ring,
    supportFn_add_two_pi]

/-- **Prop 2.5.4** (vertices): `v⁺_{M K}(t) = M v⁻_K(ω + π/2 - t)`. -/
theorem vtxP_mirror (S : Set ℝ²) (ω t : ℝ) :
    vtxP (mirror ω '' S) t = mirror ω (vtxM S (ω + π / 2 - t)) := by
  apply eq_of_inner_u_v_eq (t := t)
  · rw [inner_vtxP_u, inner_mirror_u, supportFn_mirror, inner_vtxM_u]
  · rw [inner_vtxP_v, inner_mirror_v, edgeMax_mirror, inner_vtxM_v]

/-- **Prop 2.5.4** (vertices): `v⁻_{M K}(t) = M v⁺_K(ω + π/2 - t)`. -/
theorem vtxM_mirror (S : Set ℝ²) (ω t : ℝ) :
    vtxM (mirror ω '' S) t = mirror ω (vtxP S (ω + π / 2 - t)) := by
  apply eq_of_inner_u_v_eq (t := t)
  · rw [inner_vtxM_u, inner_mirror_u, supportFn_mirror, inner_vtxP_u]
  · rw [inner_vtxM_v, inner_mirror_v, edgeMin_mirror, inner_vtxP_v]

lemma edgeLength_mirror (S : Set ℝ²) (ω t : ℝ) :
    edgeLength (mirror ω '' S) t = edgeLength S (ω + π / 2 - t) := by
  rw [edgeLength, edgeLength, edgeMax_mirror, edgeMin_mirror]; ring

/-! ## Corners, wedges, gaps -/

lemma mirror_v (ω : ℝ) : mirror ω (v ω) = u 0 := by
  apply eq_of_inner_u_v_eq (t := 0)
  · rw [inner_mirror_u, inner_u_u, inner_v_u_eq_sin, show ω + π / 2 - 0 - ω = π / 2 by ring,
      sin_pi_div_two]
  · rw [inner_mirror_v, inner_u_v, inner_v_v_eq_cos, show ω + π / 2 - 0 - ω = π / 2 by ring,
      cos_pi_div_two, neg_zero]

lemma mirror_u_zero (ω : ℝ) : mirror ω (u 0) = v ω := by
  rw [← mirror_v ω, mirror_mirror]

lemma innerCorner_mirror (S : Set ℝ²) (ω t : ℝ) :
    innerCorner (mirror ω '' S) t = mirror ω (innerCorner S (ω - t)) := by
  apply eq_of_inner_u_v_eq (t := t)
  · rw [inner_innerCorner_u, inner_mirror_u, supportFn_mirror,
      show ω + π / 2 - t = ω - t + π / 2 by ring, u_add_pi_div_two, inner_innerCorner_v]
  · rw [inner_innerCorner_v, inner_mirror_v, supportFn_mirror,
      show ω + π / 2 - t = ω - t + π / 2 by ring, v_add_pi_div_two, inner_neg_right, neg_neg,
      inner_innerCorner_u, show ω + π / 2 - (t + π / 2) = ω - t by ring]

theorem wedge_mirror (S : Set ℝ²) (ω t : ℝ) :
    wedge (mirror ω '' S) ω t = mirror ω '' wedge S ω (ω - t) := by
  ext p
  rw [mem_mirror_image]
  simp only [wedge, mem_inter_iff]
  rw [← mem_fan_mirror (ω := ω), ← mirror_mirror ω p, mirror_mem_QminusS_iff, mirror_mirror]

lemma gapW_mirror (S : Set ℝ²) (ω t : ℝ) : gapW (mirror ω '' S) t = gapZ S ω (ω - t) := by
  rw [gapW, gapZ, supportFn_mirror, supportFn_mirror, sub_zero,
    show ω + π / 2 - t = ω - t + π / 2 by ring, show ω - (ω - t) = t by ring]

lemma gapZ_mirror (S : Set ℝ²) (ω t : ℝ) : gapZ (mirror ω '' S) ω t = gapW S (ω - t) := by
  rw [gapW, gapZ, supportFn_mirror, supportFn_mirror, show ω + π / 2 - (ω + π / 2) = 0 by ring,
    show ω + π / 2 - (t + π / 2) = ω - t by ring]

theorem IsCap.cornerA_mirror (hK : IsCap K ω) :
    hK.image_mirror.cornerA = Sofa.mirror ω hK.cornerC := by
  unfold IsCap.cornerA IsCap.cornerC
  rw [supportFn_mirror, mirror_smul, mirror_v, sub_zero]

theorem IsCap.cornerC_mirror (hK : IsCap K ω) :
    hK.image_mirror.cornerC = Sofa.mirror ω hK.cornerA := by
  unfold IsCap.cornerA IsCap.cornerC
  rw [supportFn_mirror, mirror_smul, mirror_u_zero,
    show ω + π / 2 - (ω + π / 2) = 0 by ring]

end Sofa
