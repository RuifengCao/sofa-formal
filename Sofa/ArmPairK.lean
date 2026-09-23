/-
# Sofa/ArmPairK.lean — packaging a balanced maximum cap as an `ArmPair`

`Sofa/ArmBound.lean` reduces Baek's Theorem 6.5.6 (`f_K, g_K > 1`) to a purely one-dimensional
statement about a pair of continuous functions (`ArmPair`).  Rounds 21–25 supplied every
ingredient except continuity:

* `bound_f` — `1 + ∫_0^t m₀(g_K) ≤ f_K(t)` (`one_add_integral_le_armFp`, round 25);
* `bound_G` — the same for the mirror cap, which by Prop 6.2.2 is exactly `bound_f` for `K^m`;
* `nonneg` — `armFm_nonneg` (round 24).

This file supplies the continuity.  Since `σ_K` has no atoms on `[0, π/2)` (rounds 23 and 25),
`v⁻_K = v⁺_K` there, so `v⁻_K` is two-sided continuous on `[0, π/2)` and left-continuous at `π/2`:
`f⁻_K` is continuous on `[0, π/2]`.  Clamping the argument gives a globally continuous

    `F_K(t) := f⁻_K(max 0 (min t (π/2)))`     (`armFK`)

with `F_K = f⁺_K` on `[0, π/2)` and `F_K(0) = 1`, and `G := F_{K^m}` satisfies
`G(π/2 − u) = g⁺_K(u)` on `[0, π/2]`.  Hence `ArmPair F_K F_{K^m}`, and `one_lt_of_armPair`
gives **Theorem 6.5.6**.

STATUS: [PROOF-C-local] round 1 (2026-09-22, Opus 5).
-/
import Sofa.EndPoint
import Sofa.MirrorArm

noncomputable section

open Real Set Filter Topology MeasureTheory Metric
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²}

/-! ## The missing mirror identity -/

/-- **Baek Prop 6.2.2**: `f⁻_{M_ω K}(t) = g⁺_K(ω − t)`. -/
theorem armFm_mirror (S : Set ℝ²) (ω t : ℝ) :
    armFm (mirror ω '' S) t = armGp S (ω - t) := by
  rw [armFm, armGp, outerCorner_mirror, vtxM_mirror,
    show ω + π / 2 - t = ω - t + π / 2 by ring, ← mirror_sub, inner_mirror_v,
    show ω + π / 2 - t = ω - t + π / 2 by ring, v_add_pi_div_two, inner_neg_right, neg_neg]

/-! ## `v⁻_K = v⁺_K` on `[0, π/2)` and continuity on `[0, π/2]` -/

theorem edgeLength_eq_zero_Ico (hK : IsBalancedMaxCap K (π / 2)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht2 : t < π / 2) : edgeLength K t = 0 := by
  rcases eq_or_lt_of_le ht0 with heq | hlt
  · rw [← heq]; exact edgeLength_zero_of_balanced hK
  · exact edgeLength_eq_zero_of_balanced hK hlt ht2

theorem vtxM_eq_vtxP_Ico (hK : IsBalancedMaxCap K (π / 2)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht2 : t < π / 2) : vtxM K t = vtxP K t := by
  have h := vtxP_sub_vtxM K t
  rw [edgeLength_eq_zero_Ico hK ht0 ht2, zero_smul, sub_eq_zero] at h
  exact h.symm

theorem continuousOn_vtxM_Icc (hK : IsBalancedMaxCap K (π / 2)) :
    ContinuousOn (vtxM K) (Icc 0 (π / 2)) := by
  have hKc := hK.1.isCompact
  have hKne := hK.1.nonempty
  intro t ht
  have hL : ContinuousWithinAt (vtxM K) (Iic t) t := continuousWithinAt_vtxM hKc hKne t
  rcases eq_or_lt_of_le ht.2 with heq | hlt
  · -- `t = π/2`: only the left side of `Icc 0 (π/2)` matters
    refine hL.mono ?_
    rw [heq]
    exact Icc_subset_Iic_self
  · have hR : ContinuousWithinAt (vtxM K) (Ico t (π / 2)) t := by
      refine ContinuousWithinAt.congr
        ((continuousWithinAt_vtxP hKc hKne t).mono Ico_subset_Ici_self) (fun y hy => ?_) ?_
      · exact vtxM_eq_vtxP_Ico hK (le_trans ht.1 hy.1) hy.2
      · exact vtxM_eq_vtxP_Ico hK ht.1 hlt
    refine (hL.union hR).mono_of_mem_nhdsWithin ?_
    have hmem : Icc 0 (π / 2) ∩ Iio (π / 2) ∈ 𝓝[Icc 0 (π / 2)] t :=
      inter_mem_nhdsWithin _ (Iio_mem_nhds hlt)
    refine mem_of_superset hmem ?_
    rintro y ⟨hy1, hy2⟩
    rcases le_or_gt y t with hyt | hyt
    · exact Or.inl hyt
    · exact Or.inr ⟨hyt.le, hy2⟩

theorem continuousOn_armFm_Icc (hK : IsBalancedMaxCap K (π / 2)) :
    ContinuousOn (armFm K) (Icc 0 (π / 2)) := by
  have he : armFm K = fun t => supportFn K (t + π / 2) - ⟪vtxM K t, v t⟫ := by
    funext t; rw [armFm_eq, inner_vtxM_v]
  rw [he]
  refine ContinuousOn.sub ?_ ?_
  · exact ((continuous_supportFn hK.1.isCompact hK.1.nonempty).comp
      (continuous_id.add continuous_const)).continuousOn
  · exact (continuousOn_vtxM_Icc hK).inner (continuous_v.continuousOn)

/-! ## The clamped arm length -/

/-- Baek's `f_K`, as a globally continuous function: `f⁻_K` with the argument clamped to
`[0, π/2]`.  On `[0, π/2)` it agrees with `f⁺_K`. -/
def armFK (K : Set ℝ²) (t : ℝ) : ℝ := armFm K (max 0 (min t (π / 2)))

lemma clamp_mem (t : ℝ) : max 0 (min t (π / 2)) ∈ Icc (0:ℝ) (π / 2) :=
  ⟨le_max_left _ _, max_le (by positivity) (min_le_right _ _)⟩

lemma continuous_clamp : Continuous fun t : ℝ => max 0 (min t (π / 2)) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem continuous_armFK (hK : IsBalancedMaxCap K (π / 2)) : Continuous (armFK K) :=
  (continuousOn_armFm_Icc hK).comp_continuous continuous_clamp clamp_mem

theorem armFK_nonneg (hK : IsBalancedMaxCap K (π / 2)) (t : ℝ) : 0 ≤ armFK K t :=
  armFm_nonneg hK.1.isCompact hK.1.nonempty _

theorem armFK_of_mem {t : ℝ} (ht : t ∈ Icc (0:ℝ) (π / 2)) : armFK K t = armFm K t := by
  rw [armFK, min_eq_left ht.2, max_eq_right ht.1]

theorem armFK_zero (hK : IsBalancedMaxCap K (π / 2)) : armFK K 0 = 1 := by
  rw [armFK_of_mem ⟨le_rfl, by positivity⟩, armFm_zero_of_isCap hK.1]

theorem armFK_eq_armFp (hK : IsBalancedMaxCap K (π / 2)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht2 : t < π / 2) : armFK K t = armFp K t := by
  have h : edgeMin K t = edgeMax K t := by
    have hz := edgeLength_eq_zero_Ico hK ht0 ht2
    rw [edgeLength, sub_eq_zero] at hz
    exact hz.symm
  rw [armFK_of_mem ⟨ht0, ht2.le⟩, armFm_eq, armFp_eq, h]

/-! ## `G(π/2 − u) = g⁺_K(u)`, and the `ArmPair` bound -/

theorem armFK_mirror_sub {u : ℝ} (hu0 : 0 ≤ u) (hu2 : u ≤ π / 2) :
    armFK (mirror (π / 2) '' K) (π / 2 - u) = armGp K u := by
  rw [armFK_of_mem ⟨by linarith, by linarith⟩, armFm_mirror, sub_sub_cancel]

lemma intervalIntegrable_m0_armGp (hKc : IsCompact K) (hKne : K.Nonempty) (a b : ℝ) :
    IntervalIntegrable (fun u => m0 (armGp K u)) volume a b := by
  have he : (fun u => m0 (armGp K u)) = fun u => armGp K u - k0 (armGp K u) := rfl
  rw [he]
  exact (intervalIntegrable_armGp hKc hKne a b).sub
    (intervalIntegrable_k0_comp (intervalIntegrable_armGp hKc hKne a b))

theorem integral_armFK_mirror {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ π / 2) :
    (∫ u in (0:ℝ)..t, m0 (armFK (mirror (π / 2) '' K) (π / 2 - u)))
      = ∫ u in (0:ℝ)..t, m0 (armGp K u) := by
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le ht0] at hu
  rw [armFK_mirror_sub hu.1 (le_trans hu.2 ht2)]

/-- `f⁻_K` is left-continuous at `π/2` (`v⁻_K` always is). -/
theorem tendsto_armFm_nhdsLT (hKc : IsCompact K) (hKne : K.Nonempty) (a : ℝ) :
    Tendsto (armFm K) (𝓝[<] a) (𝓝 (armFm K a)) := by
  have hv : Tendsto (fun s : ℝ => v s) (𝓝[<] a) (𝓝 (v a)) :=
    (continuous_v.tendsto a).mono_left nhdsWithin_le_nhds
  have hvtx : Tendsto (fun s => ⟪vtxM K s, v s⟫) (𝓝[<] a) (𝓝 ⟪vtxM K a, v a⟫) :=
    (tendsto_vtxM_left hKc hKne a).inner hv
  have hsup : Tendsto (fun s : ℝ => supportFn K (s + π / 2)) (𝓝[<] a)
      (𝓝 (supportFn K (a + π / 2))) :=
    ((((continuous_supportFn hKc hKne).comp
      (continuous_id.add continuous_const)).tendsto a)).mono_left nhdsWithin_le_nhds
  have he : armFm K = fun s => supportFn K (s + π / 2) - ⟪vtxM K s, v s⟫ := by
    funext s; rw [armFm_eq, inner_vtxM_v]
  rw [he]
  exact hsup.sub hvtx

/-- **`bound_f`**: `1 + ∫_0^t m₀(G(π/2 − u)) du ≤ F_K(t)` on `[0, π/2]`. -/
theorem armFK_bound (hK : IsBalancedMaxCap K (π / 2)) :
    ∀ t ∈ Icc (0:ℝ) (π / 2),
      1 + ∫ u in (0:ℝ)..t, m0 (armFK (mirror (π / 2) '' K) (π / 2 - u)) ≤ armFK K t := by
  have hpi := pi_pos
  have hKc := hK.1.isCompact
  have hKne := hK.1.nonempty
  intro t ht
  rw [integral_armFK_mirror ht.1 ht.2]
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0, intervalIntegral.integral_same, add_zero, armFK_zero hK]
  · -- take the limit from the left at `t`
    rw [armFK_of_mem ⟨ht.1, ht.2⟩]
    have hlhs : Tendsto (fun T : ℝ => 1 + ∫ u in (0:ℝ)..T, m0 (armGp K u)) (𝓝[<] t)
        (𝓝 (1 + ∫ u in (0:ℝ)..t, m0 (armGp K u))) := by
      have hcont := intervalIntegral.continuous_primitive
        (fun a b => intervalIntegrable_m0_armGp hKc hKne a b) (0:ℝ)
      exact (tendsto_const_nhds.add (hcont.tendsto t)).mono_left nhdsWithin_le_nhds
    have hrhs := tendsto_armFm_nhdsLT hKc hKne t
    refine le_of_tendsto_of_tendsto hlhs hrhs ?_
    filter_upwards [Ioo_mem_nhdsLT h0] with T hT
    have hTlt : T < π / 2 := lt_of_lt_of_le hT.2 ht.2
    have heq : armFm K T = armFp K T := by
      rw [← armFK_of_mem ⟨hT.1.le, hTlt.le⟩, armFK_eq_armFp hK hT.1.le hTlt]
    rw [heq]
    exact one_add_integral_le_armFp hK hT.1 hTlt

/-! ## Theorem 6.5.6 -/

theorem armPair_balanced (hK : IsBalancedMaxCap K (π / 2)) :
    ArmPair (armFK K) (armFK (mirror (π / 2) '' K)) := by
  have hpi := pi_pos
  have hM := hK.image_mirror_le (by linarith : (0:ℝ) < π / 2) le_rfl
  refine ⟨continuous_armFK hK, continuous_armFK hM, armFK_nonneg hK, armFK_nonneg hM,
    armFK_bound hK, ?_⟩
  intro t ht
  have h := armFK_bound hM t ht
  rwa [mirror_image_mirror_image] at h

/-- **Baek Theorem 6.5.6**: `f⁺_K(t) > 1` for every balanced maximum cap and `t ∈ (0, π/2)`. -/
theorem one_lt_armFp_of_balanced (hK : IsBalancedMaxCap K (π / 2)) {t : ℝ}
    (ht0 : 0 < t) (ht2 : t < π / 2) : 1 < armFp K t := by
  have h := (one_lt_of_armPair (armPair_balanced hK) ht0 ht2.le).1
  rwa [armFK_eq_armFp hK ht0.le ht2] at h

/-- **Baek Theorem 6.5.6**: `g⁺_K(t) > 1` for every balanced maximum cap and `t ∈ (0, π/2)`. -/
theorem one_lt_armGp_of_balanced (hK : IsBalancedMaxCap K (π / 2)) {t : ℝ}
    (ht0 : 0 < t) (ht2 : t < π / 2) : 1 < armGp K t := by
  have hpi := pi_pos
  have h := (one_lt_of_armPair (armPair_balanced hK)
    (show (0:ℝ) < π / 2 - t by linarith) (by linarith)).2
  rwa [armFK_mirror_sub ht0.le ht2.le] at h

/-! ## Proposition 6.4.6 (1): continuity of the arm lengths -/

/-- `g⁺_K` is continuous on all of `[0, π/2]`: by Prop 6.2.2 it *is* `f⁻_{K^m}(π/2 − ·)`. -/
theorem continuousOn_armGp_Icc (hK : IsBalancedMaxCap K (π / 2)) :
    ContinuousOn (armGp K) (Icc 0 (π / 2)) := by
  have hpi := pi_pos
  have hM := hK.image_mirror_le (by linarith : (0:ℝ) < π / 2) le_rfl
  have he : armGp K = fun r => armFm (mirror (π / 2) '' K) (π / 2 - r) := by
    funext r; rw [armFm_mirror, sub_sub_cancel]
  rw [he]
  refine (continuousOn_armFm_Icc hM).comp (continuous_const.sub continuous_id).continuousOn ?_
  rintro r ⟨hr0, hr2⟩
  exact ⟨by simpa using (by linarith : (0:ℝ) ≤ π / 2 - r), by simpa using (by linarith : π / 2 - r ≤ π / 2)⟩

/-- `f⁺_K` is continuous on `[0, π/2)`.  **Not** on the closed interval: at `π/2` the left limit
is `f⁻_K(π/2)`, and `f⁺_K(π/2) − f⁻_K(π/2) = σ_K({π/2}) = |e_K(π/2)|` is the length of the top
face of the cap, which is positive for Gerver's sofa.  Baek's `f_K` on `[0, π/2]` (Def 6.4.1 +
Prop 6.4.6 (1)) is the continuous extension, i.e. `armFK` above. -/
theorem continuousOn_armFp_Ico (hK : IsBalancedMaxCap K (π / 2)) :
    ContinuousOn (armFp K) (Ico 0 (π / 2)) := by
  refine ContinuousOn.congr ((continuousOn_armFm_Icc hK).mono Ico_subset_Icc_self) ?_
  intro t ht
  have h : edgeMin K t = edgeMax K t := by
    have hz := edgeLength_eq_zero_Ico hK ht.1 ht.2
    rw [edgeLength, sub_eq_zero] at hz
    exact hz.symm
  rw [armFp_eq, armFm_eq, h]

end Sofa
