/-
# Sofa/Motion.lean — building upstream motions `I → E(2)` (M2 / M-H infrastructure)

* `continuous_motion_of_continuous_apply`: a family of rigid motions is continuous for the
  upstream topology on `E(2)` as soon as every orbit `x ↦ m x q` is continuous.
* coordinates of clockwise rotations, continuity of `u`, `v`, `rot`,
  and `rotateTranslate` in terms of `rot`.

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 1 (2026-09-17, Opus 5): compiled in the cloud dev tree
(Lean 4.33.1, Mathlib v4.33.1 with subset imports), no `sorry`; full `import Mathlib` re-check pending.
-/
import Sofa.RotationAngle

noncomputable section

open Real Set MovingSofa
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa

/-- A family of rigid motions is continuous (for the upstream topology on `E(2)`) as soon as
every orbit `x ↦ m x q` is continuous (`ℝ²` is finite dimensional). -/
theorem continuous_motion_of_continuous_apply {X : Type*} [TopologicalSpace X] {m : X → E(2)}
    (h : ∀ q, Continuous fun x => m x q) : Continuous m := by
  rw [continuous_induced_rng]
  let D := ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ ℝ² ℝ²
  have hsymm : ∀ (f : ℝ² →ᴬ[ℝ] ℝ²) (y : ℝ²), f y = (D f).2 y + (D f).1 := by
    intro f y
    have e := ContinuousAffineMap.decompLinearIsometryEquiv_symm_apply ℝ ℝ ℝ² ℝ² (D f) y
    rwa [LinearIsometryEquiv.symm_apply_apply] at e
  have hfst : ∀ f : ℝ² →ᴬ[ℝ] ℝ², (D f).1 = f 0 := fun _ => rfl
  have hcoe : ∀ (x : X) (y : ℝ²), (m x).toAffineIsometry.toContinuousAffineMap y = m x y :=
    fun _ _ => rfl
  have h1 : Continuous fun x => (D (m x).toAffineIsometry.toContinuousAffineMap).1 := by
    simp only [hfst, hcoe]
    exact h 0
  have h2 : Continuous fun x => (D (m x).toAffineIsometry.toContinuousAffineMap).2 := by
    refine continuous_clm_apply.2 fun y => ?_
    have key : ∀ x, (D (m x).toAffineIsometry.toContinuousAffineMap).2 y = m x y - m x 0 := by
      intro x
      have e := hsymm (m x).toAffineIsometry.toContinuousAffineMap y
      rw [hfst, hcoe, hcoe] at e
      rw [e]; abel
    simp only [key]
    exact (h y).sub (h 0)
  have h3 := D.symm.continuous.comp (h1.prodMk h2)
  refine h3.congr fun x => ?_
  simp only [Function.comp_apply, Prod.mk.eta, LinearIsometryEquiv.symm_apply_apply]

/-! ## Rotations in coordinates -/

lemma u_eq_smul (t : ℝ) : u t = cos t • e₀ + sin t • e₁ := by
  ext i; fin_cases i <;> simp [u, e₀, e₁]

lemma v_eq_smul (t : ℝ) : v t = (-sin t) • e₀ + cos t • e₁ := by
  ext i; fin_cases i <;> simp [v, e₀, e₁]

lemma continuous_u : Continuous u := by
  have : u = fun t => cos t • e₀ + sin t • e₁ := funext u_eq_smul
  rw [this]; fun_prop

lemma continuous_v : Continuous v := by
  have : v = fun t => (-sin t) • e₀ + cos t • e₁ := funext v_eq_smul
  rw [this]; fun_prop

lemma continuous_coord (i : Fin 2) : Continuous fun p : ℝ² => p i := by fun_prop

lemma continuous_rot_apply {X : Type*} [TopologicalSpace X] {θ : X → ℝ} {p : X → ℝ²}
    (hθ : Continuous θ) (hp : Continuous p) : Continuous fun x => rot (θ x) (p x) := by
  have : (fun x => rot (θ x) (p x)) = fun x => p x 0 • u (θ x) + p x 1 • v (θ x) := by
    funext x; exact rot_eq_smul _ _
  rw [this]
  have h0 : Continuous fun x => p x 0 := (continuous_coord 0).comp hp
  have h1 : Continuous fun x => p x 1 := (continuous_coord 1).comp hp
  exact (h0.smul (continuous_u.comp hθ)).add (h1.smul (continuous_v.comp hθ))

/-- `R_{-t} w = (⟪w, u_t⟫, ⟪w, v_t⟫)`. -/
lemma rot_neg_coord_zero (t : ℝ) (w : ℝ²) : rot (-t) w 0 = ⟪w, u t⟫ := by
  rw [rot_coord_zero, inner_eq, u_coord_zero, u_coord_one, cos_neg, sin_neg]; ring

lemma rot_neg_coord_one (t : ℝ) (w : ℝ²) : rot (-t) w 1 = ⟪w, v t⟫ := by
  rw [rot_coord_one, inner_eq, v_coord_zero, v_coord_one, cos_neg, sin_neg]; ring

/-- The upstream `rotateTranslate` in terms of `rot`. -/
lemma rotateTranslate_apply_eq_rot (t : ℝ) (p q : ℝ²) :
    rotateTranslate (t : Real.Angle) p q = rot t (q + p) := by
  rw [rotateTranslate_apply, rot_eq_rotation]

/-! ## Points of the plane -/

/-- The point `(a, b)`. -/
def pt (a b : ℝ) : ℝ² := a • e₀ + b • e₁

@[simp] lemma pt_zero (a b : ℝ) : pt a b 0 = a := by simp [pt, e₀, e₁]
@[simp] lemma pt_one (a b : ℝ) : pt a b 1 = b := by simp [pt, e₀, e₁]

lemma eq_pt (p : ℝ²) : p = pt (p 0) (p 1) := decomp_e p

lemma continuous_pt : Continuous fun ab : ℝ × ℝ => pt ab.1 ab.2 := by unfold pt; fun_prop
lemma continuous_pt_left (b : ℝ) : Continuous fun a => pt a b := by unfold pt; fun_prop
lemma continuous_pt_right (a : ℝ) : Continuous fun b => pt a b := by unfold pt; fun_prop

lemma le_one_of_sq_le_one {a : ℝ} (h : a ^ 2 ≤ 1) : a ≤ 1 := by nlinarith

end Sofa
