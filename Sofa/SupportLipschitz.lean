/-
# Sofa/SupportLipschitz.lean — continuity of support functions (M2 infrastructure)

The support function of a compact set contained in the ball of radius `R` is `R`-Lipschitz in
the angle.  Needed for the continuity of the supporting hallway `t ↦ L_S(t)` (the motion of the
monotone hull, Thm 2.3.2) and throughout Chapters 3–8.

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 1 (2026-09-17, Opus 5): compiled in the cloud dev tree
(Lean 4.33.1, Mathlib v4.33.1 with subset imports), no `sorry`; full `import Mathlib` re-check pending.
-/
import Sofa.Support

noncomputable section

open Real Set
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

/-- `‖u_t - u_s‖ ≤ |t - s|`. -/
lemma norm_u_sub_u_le (t s : ℝ) : ‖u t - u s‖ ≤ |t - s| := by
  have h := norm_sub_sq_real (u t) (u s)
  rw [norm_u, norm_u, inner_u_u_eq_cos] at h
  have hc : 1 - (t - s) ^ 2 / 2 ≤ cos (t - s) := one_sub_sq_div_two_le_cos
  rw [← sq_le_sq₀ (norm_nonneg _) (abs_nonneg _), sq_abs]
  nlinarith

/-- One half of the Lipschitz estimate. -/
lemma supportFn_le_add {S : Set ℝ²} (hS : IsCompact S) (hne : S.Nonempty) {R : ℝ}
    (hR : ∀ p ∈ S, ‖p‖ ≤ R) (t s : ℝ) : supportFn S t ≤ supportFn S s + R * |t - s| := by
  rw [supportFn_le_iff hS hne]
  intro p hp
  have h1 : ⟪p, u t⟫ = ⟪p, u s⟫ + ⟪p, u t - u s⟫ := by rw [inner_sub_right]; ring
  have h2 : ⟪p, u t - u s⟫ ≤ ‖p‖ * ‖u t - u s‖ := real_inner_le_norm _ _
  have h3 : ‖p‖ * ‖u t - u s‖ ≤ R * |t - s| :=
    mul_le_mul (hR p hp) (norm_u_sub_u_le t s) (norm_nonneg _) ((norm_nonneg p).trans (hR p hp))
  linarith [le_supportFn hS hp s]

/-- **Lipschitz estimate**: `|h_S(t) - h_S(s)| ≤ R |t - s|` if `S ⊆ closedBall 0 R`. -/
lemma abs_supportFn_sub_le {S : Set ℝ²} (hS : IsCompact S) (hne : S.Nonempty) {R : ℝ}
    (hR : ∀ p ∈ S, ‖p‖ ≤ R) (t s : ℝ) :
    |supportFn S t - supportFn S s| ≤ R * |t - s| := by
  have h1 := supportFn_le_add hS hne hR t s
  have h2 := supportFn_le_add hS hne hR s t
  rw [abs_sub_comm s t] at h2
  rw [abs_le]
  constructor <;> linarith

/-- The support function of a nonempty compact set is continuous. -/
theorem continuous_supportFn {S : Set ℝ²} (hS : IsCompact S) (hne : S.Nonempty) :
    Continuous (supportFn S) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hS.isBounded
  refine (LipschitzWith.of_dist_le' (f := supportFn S) (K := R) fun t s => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq]
  exact abs_supportFn_sub_le hS hne hR t s

end Sofa
