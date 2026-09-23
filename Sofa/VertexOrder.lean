/-
# Sofa/VertexOrder.lean — the angular order of `t ↦ v⁺_K(t)`

Step 5(d) of Thm 7.1.3 needs to know that the partition of the circle by the rays through the
vertices `v⁺_K(t_j)` really is a partition.  Everything reduces to the behaviour of

    `g_ψ(t) := ⟪v⁺_K(t), u_ψ⟫`

for a *fixed* direction `u_ψ`, because `A × q = ‖q‖ ⟪A, u_ψ⟫` with `u_ψ ∝ R_{−π/2} q`.

By **Theorem 5.2.2**, `g_ψ(t) − g_ψ(s) = ∫_{(s,t]} ⟪v_r, u_ψ⟫ σ_K(dr) = −∫_{(s,t]} sin(r−ψ) σ_K(dr)`.
So `g_ψ` is **nondecreasing on `[ψ−π, ψ]` and nonincreasing on `[ψ, ψ+π]`** — unimodal over a
full period, with `g_ψ(ψ) = h_K(ψ) > 0` and `g_ψ(ψ ± π) = −h_K(ψ ± π) < 0`.  Hence
`{t : g_ψ(t) > 0}` is an arc, which is exactly the "cyclic interval" property that makes the wedge
decomposition a partition.

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.AreaThm
import Sofa.Mirror

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²}

/-! ## `2π`-periodicity of the vertex -/

lemma v_add_two_pi (t : ℝ) : v (t + 2 * π) = v t := by
  rw [← u_add_pi_div_two, ← u_add_pi_div_two, show t + 2 * π + π / 2 = t + π / 2 + 2 * π by ring,
    u_add_two_pi]

lemma edge_add_two_pi (K : Set ℝ²) (t : ℝ) : edge K (t + 2 * π) = edge K t := by
  rw [edge, edge, supportLine, supportLine, supportFn_add_two_pi, line, line]
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq, u_add_two_pi]

lemma edgeMax_add_two_pi (K : Set ℝ²) (t : ℝ) : edgeMax K (t + 2 * π) = edgeMax K t := by
  rw [edgeMax, edgeMax, edge_add_two_pi,
    show t + 2 * π + π / 2 = t + π / 2 + 2 * π by ring, supportFn_add_two_pi]

theorem vtxP_add_two_pi (K : Set ℝ²) (t : ℝ) : vtxP K (t + 2 * π) = vtxP K t := by
  rw [vtxP, vtxP, supportFn_add_two_pi, edgeMax_add_two_pi, u_add_two_pi, v_add_two_pi]

/-! ## Unimodality of `t ↦ ⟪v⁺_K(t), u_ψ⟫` -/

/-- On `[ψ − π, ψ]` the projection `⟪v⁺_K(t), u_ψ⟫` is nondecreasing. -/
theorem inner_vtxP_mono (hK : IsCompact K) (hne : K.Nonempty) {ψ s t : ℝ} (hst : s ≤ t)
    (hs : ψ - π ≤ s) (ht : t ≤ ψ) : ⟪vtxP K s, u ψ⟫ ≤ ⟪vtxP K t, u ψ⟫ := by
  have h := inner_vtxP_sub_eq_setIntegral hK hne (u ψ) hst
  rw [inner_sub_left] at h
  have hnn : 0 ≤ ∫ r in Ioc s t, ⟪v r, u ψ⟫ ∂(sigmaK K) := by
    refine setIntegral_nonneg measurableSet_Ioc fun r hr => ?_
    have he := neg_inner_v_u r ψ
    have hsin : sin (r - ψ) ≤ 0 :=
      sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [hr.2]) (by linarith [hr.1])
    linarith
  linarith

/-- On `[ψ, ψ + π]` the projection `⟪v⁺_K(t), u_ψ⟫` is nonincreasing. -/
theorem inner_vtxP_anti (hK : IsCompact K) (hne : K.Nonempty) {ψ s t : ℝ} (hst : s ≤ t)
    (hs : ψ ≤ s) (ht : t ≤ ψ + π) : ⟪vtxP K t, u ψ⟫ ≤ ⟪vtxP K s, u ψ⟫ := by
  have h := inner_vtxP_sub_eq_setIntegral hK hne (u ψ) hst
  rw [inner_sub_left] at h
  have hnp : (∫ r in Ioc s t, ⟪v r, u ψ⟫ ∂(sigmaK K)) ≤ 0 := by
    rw [← neg_nonneg, ← integral_neg]
    refine setIntegral_nonneg measurableSet_Ioc fun r hr => ?_
    have he := neg_inner_v_u r ψ
    have hsin : 0 ≤ sin (r - ψ) :=
      sin_nonneg_of_nonneg_of_le_pi (by linarith [hr.1]) (by linarith [hr.2])
    linarith
  linarith

/-! ## The sign of `⟪v⁺_K(t), u_ψ⟫` near `ψ` and near `ψ + π` -/

/-- The frame formula `⟪v⁺_K(t), u_ψ⟫ = cos(ψ−t) h_K(t) + sin(ψ−t) ⟪v⁺_K(t), v_t⟫`. -/
lemma inner_vtxP_frame (K : Set ℝ²) (ψ t : ℝ) :
    ⟪vtxP K t, u ψ⟫ = cos (ψ - t) * supportFn K t + sin (ψ - t) * edgeMax K t := by
  rw [inner_u_rotate (vtxP K t) ψ t, inner_vtxP_u, inner_vtxP_v]

/-- Near `ψ` the projection is positive, quantitatively. -/
theorem inner_vtxP_pos_near {hm R : ℝ} (h : AreaSetup K hm R) {ψ t ε : ℝ}
    (hε0 : 0 ≤ ε) (hεπ : ε < π / 2) (hclose : |t - ψ| ≤ ε)
    (hsmall : R * sin ε < hm * cos ε) : 0 < ⟪vtxP K t, u ψ⟫ := by
  have habs : |ψ - t| ≤ ε := by rwa [abs_sub_comm]
  have hcos : cos ε ≤ cos (ψ - t) := by
    have h1 := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (ψ - t))
      (by linarith [pi_pos] : ε ≤ π) habs
    rwa [cos_abs] at h1
  have hcos0 : 0 < cos ε := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hεπ⟩
  obtain ⟨hd1, hd2⟩ := abs_le.1 habs
  have hsinb : |sin (ψ - t)| ≤ sin ε := by
    rcases le_or_gt 0 (ψ - t) with hpos | hneg
    · rw [abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hpos (by linarith [pi_pos]))]
      exact sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) hd2
    · rw [abs_of_nonpos (sin_nonpos_of_nonpos_of_neg_pi_le hneg.le (by linarith [pi_pos])),
        ← sin_neg]
      exact sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hsin0 : 0 ≤ sin ε := sin_nonneg_of_nonneg_of_le_pi hε0 (by linarith [pi_pos])
  have hEm : |edgeMax K t| ≤ R := by
    rw [← inner_vtxP_v]
    refine le_trans ?_ (h.norm_le _ (vtxP_mem h.isCompact h.nonempty t))
    have hcs := abs_real_inner_le_norm (vtxP K t) (v t)
    rwa [norm_v, mul_one] at hcs
  have hEb := abs_le.1 hEm
  have hSb := abs_le.1 hsinb
  have hhm := h.hm_le t
  have hm0 := h.hm_pos
  rw [inner_vtxP_frame]
  nlinarith only [hcos, hcos0, hsinb, hsin0, hEb.1, hEb.2, hSb.1, hSb.2, hhm, hm0, hsmall,
    h.R_nonneg]

/-- Near `ψ + π` the projection is negative. -/
theorem inner_vtxP_neg_near {hm R : ℝ} (h : AreaSetup K hm R) {ψ t ε : ℝ}
    (hε0 : 0 ≤ ε) (hεπ : ε < π / 2) (hclose : |t - (ψ + π)| ≤ ε)
    (hsmall : R * sin ε < hm * cos ε) : ⟪vtxP K t, u ψ⟫ < 0 := by
  have hp := inner_vtxP_pos_near h hε0 hεπ hclose hsmall
  have he : u (ψ + π) = -u ψ := u_add_pi ψ
  rw [he, inner_neg_right] at hp
  linarith

end Sofa
