/-
# Sofa/MirrorArm.lean — Baek Prop 6.2.2: the arm lengths of the mirror cap

The mirror reflection `M_ω` of `Sofa/Mirror.lean` exchanges the two arms:

    `f⁺_{M K}(t) = g⁻_K(ω − t)`,   `g⁺_{M K}(t) = f⁻_K(ω − t)`.

This is what turns Theorem 6.5.1 for `K` into the second half (`bound_G`) of the `ArmPair`
package of `Sofa/ArmBound.lean`.

Contents: `mirror_u_eq`, `mirror_v_eq` (the reflection on the moving frame),
`outerCorner_mirror`, and **`armFp_mirror`**, **`armGp_mirror`** (Prop 6.2.2).

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.PolyGap
import Sofa.RightAngle

noncomputable section

open Real Set Filter Topology MeasureTheory Metric
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²}

/-! ## The reflection on the moving frame -/

lemma mirror_u_eq (ω s : ℝ) : mirror ω (u s) = u (ω + π / 2 - s) := by
  refine eq_of_inner_u_v_eq (t := ω + π / 2 - s) ?_ ?_
  · rw [inner_mirror_u, show ω + π / 2 - (ω + π / 2 - s) = s by ring, inner_u_u, inner_u_u]
  · rw [inner_mirror_v, show ω + π / 2 - (ω + π / 2 - s) = s by ring, inner_u_v, inner_u_v,
      neg_zero]

lemma mirror_v_eq (ω s : ℝ) : mirror ω (v s) = -v (ω + π / 2 - s) := by
  refine eq_of_inner_u_v_eq (t := ω + π / 2 - s) ?_ ?_
  · rw [inner_mirror_u, show ω + π / 2 - (ω + π / 2 - s) = s by ring, inner_v_u, inner_neg_left,
      inner_v_u, neg_zero]
  · rw [inner_mirror_v, show ω + π / 2 - (ω + π / 2 - s) = s by ring, inner_v_v, inner_neg_left,
      inner_v_v]

lemma mirror_neg (ω : ℝ) (p : ℝ²) : mirror ω (-p) = -mirror ω p := by
  have h := mirror_smul ω (-1) p
  simpa using h

lemma mirror_sub (ω : ℝ) (p q : ℝ²) : mirror ω (p - q) = mirror ω p - mirror ω q := by
  rw [sub_eq_add_neg, mirror_add, mirror_neg, ← sub_eq_add_neg]

/-! ## The outer corner of the mirror cap -/

theorem outerCorner_mirror (S : Set ℝ²) (ω t : ℝ) :
    outerCorner (mirror ω '' S) t = mirror ω (outerCorner S (ω - t)) := by
  refine eq_of_inner_u_v_eq (t := t) ?_ ?_
  · rw [inner_outerCorner_u, supportFn_mirror, inner_mirror_u,
      show ω + π / 2 - t = ω - t + π / 2 by ring, inner_outerCorner_u_add]
  · rw [inner_outerCorner_v, supportFn_mirror, inner_mirror_v,
      show ω + π / 2 - (t + π / 2) = ω - t by ring,
      show ω + π / 2 - t = ω - t + π / 2 by ring, v_add_pi_div_two, inner_neg_right,
      neg_neg, inner_outerCorner_u]

/-! ## Proposition 6.2.2 -/

/-- **Baek Prop 6.2.2**: `f⁺_{M_ω K}(t) = g⁻_K(ω − t)`. -/
theorem armFp_mirror (S : Set ℝ²) (ω t : ℝ) :
    armFp (mirror ω '' S) t = armGm S (ω - t) := by
  rw [armFp, armGm, outerCorner_mirror, vtxP_mirror,
    show ω + π / 2 - t = ω - t + π / 2 by ring, ← mirror_sub, inner_mirror_v,
    show ω + π / 2 - t = ω - t + π / 2 by ring, v_add_pi_div_two, inner_neg_right, neg_neg]

/-- **Baek Prop 6.2.2**: `g⁺_{M_ω K}(t) = f⁻_K(ω − t)`. -/
theorem armGp_mirror (S : Set ℝ²) (ω t : ℝ) :
    armGp (mirror ω '' S) t = armFm S (ω - t) := by
  rw [armGp, armFm, outerCorner_mirror, vtxP_mirror,
    show ω + π / 2 - (t + π / 2) = ω - t by ring, ← mirror_sub, inner_mirror_u,
    show ω + π / 2 - t = ω - t + π / 2 by ring, u_add_pi_div_two]

/-! ## The mirror of a balanced maximum cap at `ω = π/2`

`Sofa/RightAngle.lean` proves `IsBalancedMaxCap.image_mirror` for `ω < π/2`; the restriction
comes only from `mirror_oω`, whose proof divides by `cos ω`.  At `ω = π/2` the fan apex is
`o_{π/2} = (0, 1)` and the reflection is `(x, y) ↦ (−x, y)`, so it is fixed. -/

lemma oω_pi_div_two : oω (π / 2) = pt 0 1 := by
  rw [oω, sin_pi_div_two, cos_pi_div_two, sub_self, div_zero]

lemma mirror_oω_pi_div_two : mirror (π / 2) (oω (π / 2)) = oω (π / 2) := by
  rw [oω_pi_div_two]
  refine eq_of_inner_u_v_eq (t := 0) ?_ ?_
  · rw [inner_mirror_u, sub_zero, show π / 2 + π / 2 = π by ring]
    simp [inner_eq, pt_zero, pt_one, u_coord_zero, u_coord_one]
  · rw [inner_mirror_v, sub_zero, show π / 2 + π / 2 = π by ring]
    simp [inner_eq, pt_zero, pt_one, v_coord_zero, v_coord_one]

lemma mirror_oω_le {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ π / 2) : mirror ω (oω ω) = oω ω := by
  rcases lt_or_eq_of_le hω1 with hlt | heq
  · exact mirror_oω hω0 hlt
  · subst heq
    exact mirror_oω_pi_div_two

theorem IsMaxPolyCap.image_mirror_le {ω : ℝ} {Θ : Finset ℝ} (hP : PolySetup ω Θ)
    (hω1 : ω ≤ π / 2) (hsym : ∀ t ∈ Θ, ω - t ∈ Θ) (h : IsMaxPolyCap ω Θ K) :
    IsMaxPolyCap ω Θ (mirror ω '' K) := by
  refine ⟨h.1.image_mirror hP hsym, ?_, ?_⟩
  · rw [mem_mirror_image, mirror_oω_le hP.pos hω1]
    exact h.2.1
  · intro K' hK'
    rw [polySofaArea_mirror hsym]
    calc polySofaArea ω Θ K' = polySofaArea ω Θ (mirror ω '' K') :=
          (polySofaArea_mirror hsym K').symm
      _ ≤ polySofaArea ω Θ K := h.2.2 _ (hK'.image_mirror hP hsym)

theorem IsBalancedMaxCap.image_mirror_le {ω : ℝ} (hω0 : 0 < ω) (hω1 : ω ≤ π / 2)
    (h : IsBalancedMaxCap K ω) : IsBalancedMaxCap (mirror ω '' K) ω := by
  obtain ⟨hcap, n, Ks, hmono, hn, hmax, hlim⟩ := h
  refine ⟨hcap.image_mirror, n, fun i => mirror ω '' Ks i, hmono, hn, fun i => ?_, ?_⟩
  · exact (hmax i).image_mirror_le (polySetup_uniform hω0 hω1 (hn i).1) hω1
      (fun t ht => sub_mem_uniformAngles ht)
  · have hiso : Isometry (mirror ω) := by
      rw [← coe_mirrorL]; exact (mirrorL ω).isometry
    simpa only [Metric.hausdorffDist_image hiso] using hlim

/-! ## No atoms on `(π/2, π)` either -/

/-- By mirror symmetry, `σ_K` has no atoms on `(π/2, π)` either. -/
theorem edgeLength_eq_zero_of_balanced_upper (hK : IsBalancedMaxCap K (π / 2)) {s : ℝ}
    (hs0 : π / 2 < s) (hs2 : s < π) : edgeLength K s = 0 := by
  have hpi := pi_pos
  have hM := hK.image_mirror_le (by linarith) le_rfl
  have h := edgeLength_eq_zero_of_balanced hM (t := π - s) (by linarith) (by linarith)
  rwa [edgeLength_mirror, show π / 2 + π / 2 - (π - s) = s by ring] at h

/-- Hence the two arm lengths agree on `(0, π/2)` (Baek Prop 6.4.5). -/
theorem armFm_eq_armFp_of_balanced (hK : IsBalancedMaxCap K (π / 2)) {t : ℝ}
    (ht0 : 0 < t) (ht2 : t < π / 2) : armFm K t = armFp K t := by
  rw [armFm_eq, armFp_eq, ← sub_eq_zero]
  have h := edgeLength_eq_zero_of_balanced hK ht0 ht2
  rw [edgeLength, sub_eq_zero] at h
  rw [h]
  ring

theorem armGm_eq_armGp_of_balanced (hK : IsBalancedMaxCap K (π / 2)) {t : ℝ}
    (ht0 : 0 < t) (ht2 : t < π / 2) : armGm K t = armGp K t := by
  have h := edgeLength_eq_zero_of_balanced_upper hK
    (s := t + π / 2) (by linarith) (by linarith)
  have hv : vtxM K (t + π / 2) = vtxP K (t + π / 2) := by
    have := vtxP_sub_vtxM K (t + π / 2)
    rw [h, zero_smul, sub_eq_zero] at this
    exact this.symm
  rw [armGm, armGp, hv]

/-! ## The arm lengths are nonnegative (part of Baek Prop 6.4.6 (2)) -/

lemma armFp_nonneg (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) : 0 ≤ armFp K t := by
  rw [armFp_eq, sub_nonneg, ← inner_vtxP_v, ← u_add_pi_div_two]
  exact le_supportFn hK (vtxP_mem hK hne t) _

lemma armFm_nonneg (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) : 0 ≤ armFm K t := by
  rw [armFm_eq, sub_nonneg, ← inner_vtxM_v, ← u_add_pi_div_two]
  exact le_supportFn hK (vtxM_mem hK hne t) _

lemma armGp_nonneg (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) : 0 ≤ armGp K t := by
  rw [armGp_eq_add, ← inner_vtxP_v, v_add_pi_div_two, inner_neg_right]
  linarith [le_supportFn hK (vtxP_mem hK hne (t + π / 2)) t]

lemma armGm_nonneg (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) : 0 ≤ armGm K t := by
  rw [armGm_eq_add, ← inner_vtxM_v, v_add_pi_div_two, inner_neg_right]
  linarith [le_supportFn hK (vtxM_mem hK hne (t + π / 2)) t]

/-! ## Theorem 6.5.1 for the mirror cap -/

/-- **Theorem 6.5.1 for the mirror image**, which is Baek's `bound_G`:

    `g⁻_K(π/2) + ∫_0^T m₀(f⁻_K(π/2 − s)) ds ≤ g⁻_K(π/2 − T)`. -/
theorem armGm_ge_balanced (hK : IsBalancedMaxCap K (π / 2)) {T : ℝ}
    (hT0 : 0 < T) (hT2 : T < π / 2) :
    armGm K (π / 2) + ∫ s in (0:ℝ)..T, m0 (armFm K (π / 2 - s)) ≤ armGm K (π / 2 - T) := by
  have hpi := pi_pos
  have hM := hK.image_mirror_le (by linarith : (0:ℝ) < π / 2) le_rfl
  have h := armFp_ge_balanced hM hT0 hT2
  rw [armFp_mirror, armFp_mirror, sub_zero] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [armGp_mirror]

end Sofa
