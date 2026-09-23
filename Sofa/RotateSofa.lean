/-
# Sofa/RotateSofa.lean — Theorem 1.5.2 (the movement with rotation angle π/2)

STATUS: in progress (2026-09-17, Opus 5).
-/
import Sofa.PolyCap

noncomputable section

open Real Set Filter Topology MeasureTheory MovingSofa
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa

/-! ## Rotating a set -/

lemma continuous_rot (α : ℝ) : Continuous (rot α) :=
  continuous_rot_apply continuous_const continuous_id

lemma rot_sub (α : ℝ) (p q : ℝ²) : rot α (p - q) = rot α p - rot α q := by
  rw [sub_eq_add_neg, rot_add, rot_neg, ← sub_eq_add_neg]

lemma supportFn_rot_image {S : Set ℝ²} (hS : IsCompact S) (hne : S.Nonempty) (α s : ℝ) :
    supportFn (rot α '' S) s = supportFn S (s - α) := by
  have hSc : IsCompact (rot α '' S) := hS.image (continuous_rot α)
  have hSne : (rot α '' S).Nonempty := hne.image _
  refine le_antisymm ?_ ?_
  · rw [supportFn_le_iff hSc hSne]
    rintro p ⟨q, hq, rfl⟩
    rw [inner_rot_u]
    exact le_supportFn hS hq _
  · obtain ⟨q, hq, hqv⟩ := exists_supportFn_eq hS hne (s - α)
    rw [← hqv, ← inner_rot_u α s q]
    exact le_supportFn hSc ⟨q, hq, rfl⟩ s

/-! ## Rigid motions `q ↦ rot α (q − c) + w` -/

/-- The rigid motion `q ↦ rot α (q − c) + w`. -/
def rigid (α : ℝ) (c w : ℝ²) : E(2) := rotateTranslate (α : Real.Angle) (-c + rot (-α) w)

lemma rigid_apply (α : ℝ) (c w q : ℝ²) : rigid α c w q = rot α (q - c) + w := by
  rw [rigid, rotateTranslate_apply_eq_rot, rot_add, rot_add, rot_neg, rot_rot, add_neg_cancel,
    rot_zero, rot_sub]
  abel

lemma rigid_zero (α : ℝ) (c w : ℝ²) : rigid α c w 0 = rot α (-c) + w := by
  rw [rigid_apply, zero_sub]

lemma rigid_apply_eq (α : ℝ) (c w q : ℝ²) : rigid α c w q = rot α q + rigid α c w 0 := by
  rw [rigid_apply, rigid_zero, rot_sub, rot_neg]
  abel

lemma rigid_refl (c : ℝ²) : rigid 0 c c = AffineIsometryEquiv.refl ℝ ℝ² := by
  ext q
  rw [rigid_apply, rot_zero]
  simp

lemma rigid_image (α : ℝ) (c w : ℝ²) (S : Set ℝ²) :
    rigid α c w '' S = (fun p => rot α p + w) '' ((· - c) '' S) := by
  rw [Set.image_image]
  ext p
  simp only [mem_image, rigid_apply]

lemma continuous_rigid {X : Type*} [TopologicalSpace X] {α : X → ℝ} {w : X → ℝ²} (c : ℝ²)
    (hα : Continuous α) (hw : Continuous w) : Continuous fun x => rigid (α x) c (w x) := by
  refine continuous_motion_of_continuous_apply fun q => ?_
  have : (fun x => rigid (α x) c (w x) q) = fun x => rot (α x) (q - c) + w x := by
    funext x; rw [rigid_apply]
  rw [this]
  exact (continuous_rot_apply hα continuous_const).add hw

lemma coord_zero_eq_inner (p : ℝ²) : p 0 = ⟪p, u 0⟫ := by
  rw [inner_u_decomp, cos_zero, sin_zero]; ring

lemma smul_pt (s a b : ℝ) : s • pt a b = pt (s * a) (s * b) := by
  unfold pt
  rw [smul_add, smul_smul, smul_smul]

lemma coord_rot_add_zero (α : ℝ) (q v : ℝ²) : (rot α q + v) 0 = ⟪q, u (-α)⟫ + v 0 := by
  rw [coord_zero_eq_inner, inner_add_left, inner_rot_u, zero_sub, coord_zero_eq_inner]

lemma coord_rot_add_one (α : ℝ) (q v : ℝ²) : (rot α q + v) 1 = ⟪q, u (π / 2 - α)⟫ + v 1 := by
  rw [coord_one_eq_inner, inner_add_left, inner_rot_u, coord_one_eq_inner]

/-! ## Theorem 1.5.2: the extra rotation -/

open MovingSofa in
set_option maxHeartbeats 2000000 in
/-- **The core of Theorem 1.5.2.** A moving sofa `A` with rotation angle `ω < π/2` whose width in
every direction `u_t`, `t ∈ [ω, π/2]`, is at most `1` can be rotated by an extra `π/2 − ω`
inside the horizontal hallway; the rotated copy is a sofa with rotation angle `π/2`. -/
theorem isSofaWithAngle_rot_image {A : Set ℝ²} {m : I → E(2)} {θ : I → ℝ} {ω : ℝ}
    (hω1 : ω < π / 2) (hm : IsMovingSofa A m) (hθc : Continuous θ) (hθ0 : θ 0 = 0)
    (hθm : ∀ t p, m t p = rot (θ t) p + m t 0) (hθ1 : θ 1 = -ω)
    (hwidth : ∀ t : ℝ, ω ≤ t → t ≤ π / 2 → supportFn A t + supportFn A (t + π) ≤ 1) :
    IsSofaWithAngle (rot (π / 2 - ω) '' A) (π / 2) := by
  obtain ⟨φ, hφdef⟩ : ∃ φ : ℝ, φ = π / 2 - ω := ⟨_, rfl⟩
  rw [show π / 2 - ω = φ from hφdef.symm]
  have hφ0 : 0 < φ := by rw [hφdef]; linarith
  have hAne : A.Nonempty := hm.isConnected.nonempty
  have hAc : IsCompact A := hm.isCompact
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hm.isBounded
  obtain ⟨a₀, ha₀⟩ := id hAne
  have hR0 : 0 ≤ R := le_trans (norm_nonneg a₀) (hR a₀ ha₀)
  have habs : ∀ s, |supportFn A s| ≤ R := abs_supportFn_le hAc hAne hR
  obtain ⟨x₀, hx₀⟩ : ∃ x : ℝ, x = -R - 1 := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c : ℝ², c = pt x₀ (supportFn A (3 * π / 2 - φ)) := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ², c = pt x₀ (supportFn A (3 * π / 2)) := ⟨_, rfl⟩
  obtain ⟨rp, hrp⟩ : ∃ rp : I → I, rp = fun t : I => Set.projIcc 0 1 zero_le_one (3 * (t : ℝ) - 2) :=
    ⟨_, rfl⟩
  have hrpc : Continuous rp := by
    rw [hrp]
    exact continuous_projIcc.comp (by fun_prop)
  have hrp23 : ∀ t : I, (t : ℝ) = 2 / 3 → rp t = 0 := by
    intro t ht
    rw [hrp]
    simp only
    rw [ht]
    norm_num
  have hrp1 : rp 1 = 1 := by
    rw [hrp]
    simp only
    norm_num
  -- the angle
  obtain ⟨ψ, hψ⟩ : ∃ ψ : I → ℝ, ψ = fun t : I => if (t : ℝ) ≤ 1 / 3 then -(3 * (t : ℝ) * φ)
      else if (t : ℝ) ≤ 2 / 3 then -φ else θ (rp t) - φ := ⟨_, rfl⟩
  -- the translation
  obtain ⟨w, hw⟩ : ∃ w : I → ℝ², w = fun t : I =>
      if (t : ℝ) ≤ 1 / 3 then pt x₀ (supportFn A (3 * π / 2 - (φ - 3 * (t : ℝ) * φ)))
      else if (t : ℝ) ≤ 2 / 3 then (2 - 3 * (t : ℝ)) • c₁ else m (rp t) 0 := ⟨_, rfl⟩
  have hcoe : Continuous fun t : I => (t : ℝ) := continuous_subtype_val
  have hψc : Continuous ψ := by
    rw [hψ]
    refine Continuous.if_le (by fun_prop) ?_ hcoe continuous_const ?_
    · refine Continuous.if_le continuous_const ((hθc.comp hrpc).sub continuous_const) hcoe
        continuous_const ?_
      intro t ht
      rw [hrp23 t ht, hθ0]
      ring
    · intro t ht
      rw [if_pos (by rw [ht]; norm_num), ht]
      ring
  have hwc : Continuous w := by
    rw [hw]
    refine Continuous.if_le ?_ ?_ hcoe continuous_const ?_
    · exact (continuous_pt_right x₀).comp ((continuous_supportFn hAc hAne).comp (by fun_prop))
    · refine Continuous.if_le (by fun_prop) ((continuous_eval 0).comp (hm.continuous.comp hrpc))
        hcoe continuous_const ?_
      intro t ht
      rw [hrp23 t ht, hm.zero, ht]
      norm_num
    · intro t ht
      rw [if_pos (by rw [ht]; norm_num), ht, hc₁]
      norm_num
  have hψ0 : ψ 0 = 0 := by
    rw [hψ]
    simp
  have hw0 : w 0 = c₀ := by
    rw [hw]
    simp only [Set.Icc.coe_zero]
    rw [if_pos (by norm_num), hc₀]
    congr 2
    ring
  have hψ1 : ψ 1 = -(π / 2) := by
    rw [hψ]
    simp only [Set.Icc.coe_one]
    rw [if_neg (by norm_num), if_neg (by norm_num), hrp1, hθ1, hφdef]
    ring
  -- the placed set at time `t`
  have himg : ∀ t : I, (rigid (ψ t) c₀ (w t)) '' (tr c₀ (rot φ '' A))
      = (fun q => rot (ψ t + φ) q + w t) '' A := by
    intro t
    ext p
    simp only [tr, Set.mem_image]
    constructor
    · rintro ⟨y, ⟨z, ⟨q, hq, rfl⟩, rfl⟩, rfl⟩
      exact ⟨q, hq, by rw [rigid_apply, add_sub_cancel_right, rot_rot]⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨rot φ q + c₀, ⟨rot φ q, ⟨q, hq, rfl⟩, rfl⟩,
        by rw [rigid_apply, add_sub_cancel_right, rot_rot]⟩
  -- phase 1
  have hphase1 : ∀ α : ℝ, 0 ≤ α → α ≤ φ →
      (fun q => rot α q + pt x₀ (supportFn A (3 * π / 2 - α))) '' A ⊆ horizontalHallway := by
    intro α hα0 hαφ
    rintro p ⟨q, hq, rfl⟩
    rw [mem_horizontalHallway_iff, coord_rot_add_zero, coord_rot_add_one, pt_zero, pt_one]
    have h1 : ⟪q, u (-α)⟫ ≤ supportFn A (-α) := le_supportFn hAc hq _
    have h2 : ⟪q, u (π / 2 - α)⟫ ≤ supportFn A (π / 2 - α) := le_supportFn hAc hq _
    have h3 : ⟪q, u (π / 2 - α + π)⟫ ≤ supportFn A (π / 2 - α + π) := le_supportFn hAc hq _
    rw [u_add_pi, inner_neg_right] at h3
    have h4 : (3 : ℝ) * π / 2 - α = π / 2 - α + π := by ring
    have h5 := abs_le.1 (habs (-α))
    have h6 := hwidth (π / 2 - α) (by rw [hφdef] at hαφ; linarith) (by linarith)
    refine ⟨by rw [hx₀]; linarith, by rw [h4]; linarith, by rw [h4]; linarith⟩
  -- phase 2
  have hδ : supportFn A (3 * π / 2) ≤ 0 := by
    rw [supportFn_le_iff hAc hAne]
    intro q hq
    have hq1 := ((mem_horizontalHallway_iff q).1 (hm.initial hq)).2.1
    have he : ⟪q, u (3 * π / 2)⟫ = -⟪q, u (π / 2)⟫ := by
      rw [show (3 : ℝ) * π / 2 = π / 2 + π by ring, u_add_pi, inner_neg_right]
    rw [he, ← coord_one_eq_inner]
    linarith
  have hphase2 : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (fun q => rot 0 q + s • c₁) '' A ⊆ horizontalHallway := by
    intro s hs0 hs1
    have hx0le : x₀ ≤ 0 := by rw [hx₀]; linarith
    rintro p ⟨q, hq, rfl⟩
    simp only [rot_zero]
    have hqH := (mem_horizontalHallway_iff q).1 (hm.initial hq)
    have hq3 : -q 1 ≤ supportFn A (3 * π / 2) := by
      have h := le_supportFn hAc hq (3 * π / 2)
      have he : u (3 * π / 2) = -u (π / 2) := by
        rw [show (3 : ℝ) * π / 2 = π / 2 + π by ring, u_add_pi]
      rw [he, inner_neg_right, ← coord_one_eq_inner] at h
      exact h
    have e0 : (q + s • c₁) 0 = q 0 + s * x₀ := by
      rw [hc₁, smul_pt, coord_zero_eq_inner, inner_add_left, ← coord_zero_eq_inner,
        ← coord_zero_eq_inner, pt_zero]
    have e1 : (q + s • c₁) 1 = q 1 + s * supportFn A (3 * π / 2) := by
      rw [hc₁, smul_pt, coord_one_eq_inner, inner_add_left, ← coord_one_eq_inner,
        ← coord_one_eq_inner, pt_one]
    rw [mem_horizontalHallway_iff, e0, e1]
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [hqH.1]
    · nlinarith [hq3, hδ]
    · nlinarith [hqH.2.2, hδ]
  -- the containment at every time
  have hsub : ∀ t : I, (rigid (ψ t) c₀ (w t)) '' (tr c₀ (rot φ '' A)) ⊆ hallway := by
    intro t
    rw [himg t]
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    rcases le_or_gt ((t : ℝ)) (1 / 3) with h1 | h1
    · have hψt : ψ t = -(3 * (t : ℝ) * φ) := by simp only [hψ]; rw [if_pos h1]
      have hwt : w t = pt x₀ (supportFn A (3 * π / 2 - (φ - 3 * (t : ℝ) * φ))) := by
        simp only [hw]; rw [if_pos h1]
      have he : (fun q => rot (ψ t + φ) q + w t)
          = fun q => rot (φ - 3 * (t : ℝ) * φ) q
            + pt x₀ (supportFn A (3 * π / 2 - (φ - 3 * (t : ℝ) * φ))) := by
        funext q; rw [hψt, hwt]; congr 2; ring
      rw [he]
      exact (hphase1 _ (by nlinarith) (by nlinarith)).trans subset_union_left
    · rcases le_or_gt ((t : ℝ)) (2 / 3) with h2 | h2
      · have hψt : ψ t = -φ := by simp only [hψ]; rw [if_neg (not_le.2 h1), if_pos h2]
        have hwt : w t = (2 - 3 * (t : ℝ)) • c₁ := by
          simp only [hw]; rw [if_neg (not_le.2 h1), if_pos h2]
        have he : (fun q => rot (ψ t + φ) q + w t)
            = fun q => rot 0 q + (2 - 3 * (t : ℝ)) • c₁ := by
          funext q; rw [hψt, hwt]; congr 2; ring
        rw [he]
        exact (hphase2 _ (by linarith) (by linarith)).trans subset_union_left
      · have hψt : ψ t = θ (rp t) - φ := by
          simp only [hψ]; rw [if_neg (not_le.2 h1), if_neg (not_le.2 h2)]
        have hwt : w t = m (rp t) 0 := by
          simp only [hw]; rw [if_neg (not_le.2 h1), if_neg (not_le.2 h2)]
        have he : (fun q => rot (ψ t + φ) q + w t) '' A = m (rp t) '' A := by
          refine Set.image_congr fun q _ => ?_
          rw [hψt, hwt, hθm (rp t) q]
          congr 2
          ring
        rw [he]
        exact hm.subset_hallway _
  -- the initial position
  have hinit : tr c₀ (rot φ '' A) ⊆ horizontalHallway := by
    have h := himg 0
    rw [hψ0, hw0, rigid_refl] at h
    have h2 : (AffineIsometryEquiv.refl ℝ ℝ²) '' (tr c₀ (rot φ '' A)) = tr c₀ (rot φ '' A) := by
      ext p; simp
    rw [h2] at h
    rw [h, hc₀]
    have he : (fun q => rot (0 + φ) q + pt x₀ (supportFn A (3 * π / 2 - φ)))
        = fun q => rot φ q + pt x₀ (supportFn A (3 * π / 2 - φ)) := by
      funext q; rw [zero_add]
    rw [he]
    exact hphase1 φ hφ0.le le_rfl
  -- the final position
  have hfin : (rigid (ψ 1) c₀ (w 1)) '' (tr c₀ (rot φ '' A)) ⊆ verticalHallway := by
    rw [himg 1]
    have hψt : ψ 1 = θ (rp 1) - φ := by
      simp only [hψ, Set.Icc.coe_one]
      rw [if_neg (by norm_num), if_neg (by norm_num)]
    have hwt : w 1 = m (rp 1) 0 := by
      simp only [hw, Set.Icc.coe_one]
      rw [if_neg (by norm_num), if_neg (by norm_num)]
    have he : (fun q => rot (ψ 1 + φ) q + w 1) '' A = m (rp 1) '' A := by
      refine Set.image_congr fun q _ => ?_
      rw [hψt, hwt, hθm (rp 1) q]
      congr 2
      ring
    rw [he, hrp1]
    exact hm.final
  refine ⟨c₀, fun t => rigid (ψ t) c₀ (w t), ψ,
    ⟨?_, ?_, continuous_rigid c₀ hψc hwc, ?_, hinit, hsub, hfin⟩, hψc, hψ0,
    fun t p => rigid_apply_eq (ψ t) c₀ (w t) p, hψ1⟩
  · show IsConnected ((· + c₀) '' (rot φ '' A))
    exact (hm.isConnected.image (rot φ) (continuous_rot φ).continuousOn).image (· + c₀)
      (by fun_prop)
  · show IsClosed ((· + c₀) '' (rot φ '' A))
    exact ((hAc.image (continuous_rot φ)).image (continuous_add_const c₀)).isClosed
  · show rigid (ψ 0) c₀ (w 0) = _
    rw [hψ0, hw0]
    exact rigid_refl c₀

end Sofa
