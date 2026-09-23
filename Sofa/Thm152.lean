/-
# Sofa/Thm152.lean — Baek's Theorem 1.5.2 (interface (I2))

Assembles the two halves of Theorem 1.5.2:

* the **geometric** half (`Sofa/Width.lean`): a balanced maximum cap `K` with `ω ≥ arccos(5/11)`
  and `A_ω(K) ≥ 2.2` has `K \ N(K) ⊆ P_ω \ Δ_ω`, a set of width `≤ 1` in every direction
  `u_t`, `t ∈ [ω, π/2]`;
* the **kinematic** half (`Sofa/RotateSofa.lean`): such a set can be rotated by an extra
  `π/2 − ω` inside the horizontal hallway, so it is a sofa with rotation angle `π/2`.

Together with Thm 2.5.9 (`IsCap.niche_subset_iff`), Thm 2.5.10 (`IsMonotoneSofa.sofaArea_Ccap`)
and the monotone hull (Thm 2.3.9) this gives a monotone sofa of rotation angle `π/2` and area
at least `A_ω(K)`.

STATUS: [PROOF-C-local] round 1 (2026-09-17, Opus 5): compiled in the cloud dev tree, no `sorry`.
-/
import Sofa.RotateSofa
import Sofa.Width

noncomputable section

open Real Set Filter Topology MeasureTheory MovingSofa
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa

variable {ω : ℝ} {K : Set ℝ²}

/-! ## Rotations preserve the Lebesgue measure -/

/-- `R_α` as a linear isometric equivalence (Mathlib's `Orientation.rotation`). -/
def rotL (α : ℝ) : ℝ² ≃ₗᵢ[ℝ] ℝ² := EuclideanGeometry.o.rotation (α : Real.Angle)

@[simp] lemma coe_rotL (α : ℝ) : ⇑(rotL α) = rot α := by
  funext p; exact (rot_eq_rotation α p).symm

lemma volume_rot_image (α : ℝ) (S : Set ℝ²) : volume (rot α '' S) = volume S := by
  have h : rot α '' S = (rotL α).symm ⁻¹' S := by
    ext p
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨q, hq, rfl⟩
      have : (rotL α).symm (rot α q) = q := by
        rw [← coe_rotL]; exact (rotL α).symm_apply_apply q
      rwa [this]
    · intro hp
      refine ⟨(rotL α).symm p, hp, ?_⟩
      rw [← coe_rotL]
      exact (rotL α).apply_symm_apply p
  rw [h]
  exact (rotL α).symm.measurePreserving.measure_preimage_emb
    (rotL α).symm.toHomeomorph.measurableEmbedding S

/-! ## Theorem 1.5.2 -/

/-- **(I2) — Baek's Theorem 1.5.2.**  For `ω ∈ [arccos(5/11), π/2)` a balanced maximum cap `K`
with `A_ω(K) ≥ 2.2` is dominated by a *monotone sofa with rotation angle `π/2`*. -/
theorem IsBalancedMaxCap.exists_monotoneSofa_pi_div_two (hK : IsBalancedMaxCap K ω)
    (hω : arccos (5 / 11) ≤ ω) (hω1 : ω < π / 2) (harea : 2.2 ≤ sofaArea K ω) :
    ∃ T, IsMonotoneSofa T (π / 2) ∧ ENNReal.ofReal (sofaArea K ω) ≤ volume T := by
  have hω0 : 0 < ω := lt_of_lt_of_le (arccos_pos.2 (by norm_num)) hω
  have hcos : cos ω ≤ 5 / 11 := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (arccos_nonneg _)
      (by linarith [pi_pos] : ω ≤ π) hω
    rwa [Real.cos_arccos (by norm_num) (by norm_num)] at h
  -- Thm 3.5.4 + Thm 2.5.9: `K` is the cap of a monotone sofa `S`
  have hN : niche K ω ⊆ K := hK.niche_subset hω0 hω1.le
  obtain ⟨S, hSmono, hSK⟩ := (hK.1.niche_subset_iff hω0 hω1.le).1 hN
  have hSsofa : IsSofaWithAngle S ω := hSmono.isSofaWithAngle hω0 hω1.le
  have hSc : IsCompact S := hSsofa.isCompact
  have hSne : S.Nonempty := hSsofa.nonempty
  -- Thm 2.5.10: `|S| = A_ω(K)`
  have hSarea : sofaArea K ω = (volume S).toReal := by
    rw [← hSK]; exact hSmono.sofaArea_Ccap hω0 hω1.le
  -- Thm 2.4.3: `S = K \ N(K)`
  have hSeq : S = K \ niche K ω := by
    have h := hSmono.eq_Ccap_sdiff_niche hω0 hω1.le
    rwa [hSK] at h
  have hvolK : 11 / 5 ≤ volume.real K := by
    have h0 : (0 : ℝ) ≤ (volume (niche K ω)).toReal := ENNReal.toReal_nonneg
    have h1 : volume.real K = (volume K).toReal := rfl
    rw [sofaArea] at harea
    rw [h1]
    norm_num at harea ⊢
    linarith
  -- the geometric half (§1.5.1 / Thm 4.2.5)
  have hwidth : ∀ t : ℝ, ω ≤ t → t ≤ π / 2 → supportFn S t + supportFn S (t + π) ≤ 1 :=
    fun t ht1 ht2 =>
      supportFn_add_supportFn_le_one hω0 hω1 hcos hK hvolK hSeq.subset hSc hSne ht1 ht2
  -- the kinematic half (Thm 1.5.2)
  obtain ⟨c, m, θ, hm, hθc, hθ0, hθm, hθ1⟩ := hSsofa
  have hwidth' : ∀ t : ℝ, ω ≤ t → t ≤ π / 2 →
      supportFn (tr c S) t + supportFn (tr c S) (t + π) ≤ 1 := by
    intro t ht1 ht2
    rw [supportFn_tr hSc hSne, supportFn_tr hSc hSne, u_add_pi, inner_neg_right]
    have := hwidth t ht1 ht2
    linarith
  have hrot := isSofaWithAngle_rot_image hω1 hm hθc hθ0 hθm hθ1 hwidth'
  obtain ⟨T', hT'⟩ : ∃ T', T' = rot (π / 2 - ω) '' tr c S := ⟨_, rfl⟩
  rw [← hT'] at hrot
  have hvolT' : volume T' = volume S := by rw [hT', volume_rot_image, volume_tr]
  -- the monotone hull (Thm 2.3.9)
  have hpi : (0 : ℝ) < π / 2 := by positivity
  have hstd := stdPos_tr_stdVec hrot.isCompact hrot.nonempty hpi le_rfl
  have hT'' := hrot.tr' (stdVec T' (π / 2))
  obtain ⟨-, -, hsub⟩ := hT''.Imono_props hstd hpi le_rfl
  refine ⟨Imono (tr (stdVec T' (π / 2)) T') (π / 2), ⟨_, hT'', hstd, rfl⟩, ?_⟩
  calc ENNReal.ofReal (sofaArea K ω) = volume S := by
        rw [hSarea, ENNReal.ofReal_toReal hSc.measure_lt_top.ne]
    _ = volume T' := hvolT'.symm
    _ = volume (tr (stdVec T' (π / 2)) T') := (volume_tr _ _).symm
    _ ≤ _ := measure_mono hsub

end Sofa
