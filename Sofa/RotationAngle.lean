/-
# Sofa/RotationAngle.lean — the rotation angle of a continuous rigid motion (M2, batch 1)

Main result: `Sofa.exists_rotationAngle`.  For an upstream motion `m : I → E(2)`
(continuous, `m 0 = id`) there is a continuous `θ : I → ℝ` with `θ 0 = 0` and
`m t p = rot (θ t) p + m t 0` for all `t, p`  (Baek Def 2.3.3, "rotation angle").

Proof: the path `t ↦ (m t).linear e₀` lies on the unit circle; lift it through the covering map
`Circle.exp : ℝ → Circle` (`Circle.isCoveringMap_exp`, `IsCoveringMap.exists_path_lifts`); the
sign of the second basis vector is `±1`, continuous, `+1` at `t = 0`, hence `+1` (IVT).

STATUS: [PROOF-C] (round 3 compiled on the user's machine, 2026-09-17, full Mathlib) and
[PROOF-C-local] [AXIOM-CHECK] (cloud dev tree, Opus 5).  Round 2 had two small errors:
(i) a redundant `simp only`, (ii) the IVT point `0` was left as a metavariable.
-/
import Sofa.Basic

noncomputable section

open Real Set MovingSofa
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa

/-- `rot θ p = p 0 • u θ + p 1 • v θ`. -/
lemma rot_eq_smul (θ : ℝ) (p : ℝ²) : rot θ p = p 0 • u θ + p 1 • v θ := by
  ext i; fin_cases i <;> simp <;> ring

lemma e₀_eq : MovingSofa.e₀ = u 0 := by ext i; fin_cases i <;> simp [MovingSofa.e₀]
lemma e₁_eq : MovingSofa.e₁ = v 0 := by ext i; fin_cases i <;> simp [MovingSofa.e₁]

/-! ## Vectors as complex numbers -/

/-- `toC (x, y) = x + y i`. -/
def toC (w : ℝ²) : ℂ := (w 0 : ℂ) + (w 1 : ℂ) * Complex.I

@[simp] lemma toC_re (w : ℝ²) : (toC w).re = w 0 := by simp [toC]
@[simp] lemma toC_im (w : ℝ²) : (toC w).im = w 1 := by simp [toC]

lemma norm_toC {w : ℝ²} (h : w 0 ^ 2 + w 1 ^ 2 = 1) : ‖toC w‖ = 1 := by
  rw [Complex.norm_def, Complex.normSq_apply, toC_re, toC_im]
  have : w 0 * w 0 + w 1 * w 1 = 1 := by nlinarith [h]
  rw [this, Real.sqrt_one]

lemma toC_mem_unitSphere {w : ℝ²} (h : w 0 ^ 2 + w 1 ^ 2 = 1) :
    toC w ∈ Submonoid.unitSphere ℂ :=
  mem_sphere_zero_iff_norm.2 (norm_toC h)

/-- If `exp (θ i) = toC w` then `w = u θ`. -/
lemma eq_u_of_exp_eq {w : ℝ²} {θ : ℝ} (h : Complex.exp (θ * Complex.I) = toC w) : w = u θ := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  rw [Complex.exp_ofReal_mul_I_re, toC_re] at hre
  rw [Complex.exp_ofReal_mul_I_im, toC_im] at him
  ext i; fin_cases i
  · simp [← hre]
  · simp [← him]

/-! ## The rotation angle -/

/-- **Rotation angle.**  Every continuous rigid motion starting at the identity is, at each time,
a rotation by a continuously varying angle `θ t` followed by a translation. -/
theorem exists_rotationAngle {m : I → E(2)} (hm : Continuous m) (h0 : m 0 = .refl ℝ ℝ²) :
    ∃ θ : I → ℝ, Continuous θ ∧ θ 0 = 0 ∧ ∀ t p, m t p = rot (θ t) p + m t 0 := by
  -- the images of the two basis vectors under the linear part
  have hw0 : Continuous fun t => ((m t).linearIsometryEquiv MovingSofa.e₀) 0 :=
    continuous_linear_coord hm MovingSofa.e₀ 0
  have hw1 : Continuous fun t => ((m t).linearIsometryEquiv MovingSofa.e₀) 1 :=
    continuous_linear_coord hm MovingSofa.e₀ 1
  have hw'0 : Continuous fun t => ((m t).linearIsometryEquiv MovingSofa.e₁) 0 :=
    continuous_linear_coord hm MovingSofa.e₁ 0
  have hw'1 : Continuous fun t => ((m t).linearIsometryEquiv MovingSofa.e₁) 1 :=
    continuous_linear_coord hm MovingSofa.e₁ 1
  have hsq : ∀ t, ((m t).linearIsometryEquiv MovingSofa.e₀) 0 ^ 2
      + ((m t).linearIsometryEquiv MovingSofa.e₀) 1 ^ 2 = 1 :=
    fun t => sq_add_sq_eq_one _
  -- at time 0 the linear part is the identity
  have hL0 : ∀ p, (m 0).linearIsometryEquiv p = p := by
    intro p; rw [h0]; rfl
  -- the path on the unit circle (kept abstract: `hγ` is all we use)
  obtain ⟨γ, hγ⟩ : ∃ γ : C(I, Circle),
      ∀ t, (γ t : ℂ) = toC ((m t).linearIsometryEquiv MovingSofa.e₀) := by
    refine ⟨⟨fun t => ⟨toC ((m t).linearIsometryEquiv MovingSofa.e₀),
      toC_mem_unitSphere (hsq t)⟩, ?_⟩, fun t => rfl⟩
    refine Continuous.subtype_mk ?_ _
    unfold toC
    exact (Complex.continuous_ofReal.comp hw0).add
      ((Complex.continuous_ofReal.comp hw1).mul continuous_const)
  have hγ0 : γ 0 = Circle.exp 0 := by
    apply Circle.ext
    rw [hγ 0, hL0, Circle.coe_exp]
    simp [toC, MovingSofa.e₀]
  -- lift through the covering map `Circle.exp`
  obtain ⟨Θ, hΘ, hΘ0⟩ := Circle.isCoveringMap_exp.exists_path_lifts γ 0 hγ0
  -- `w t = u (Θ t)`
  have hu : ∀ t, (m t).linearIsometryEquiv MovingSofa.e₀ = u (Θ t) := by
    intro t
    apply eq_u_of_exp_eq
    have h1 : Circle.exp (Θ t) = γ t := congrFun hΘ t
    have h2 : (Circle.exp (Θ t) : ℂ) = (γ t : ℂ) := congrArg (fun z : Circle => (z : ℂ)) h1
    rw [hγ t, Circle.coe_exp] at h2
    exact h2
  -- the second basis vector is `± v (Θ t)`; the sign `sgn` is continuous and `+1` at `0`
  have horth : ∀ t, ⟪(m t).linearIsometryEquiv MovingSofa.e₁, u (Θ t)⟫ = 0 := by
    intro t
    rw [← hu t, LinearIsometryEquiv.inner_map_map, e₁_eq, e₀_eq, inner_v_u]
  have hnorm : ∀ t, ⟪(m t).linearIsometryEquiv MovingSofa.e₁,
      (m t).linearIsometryEquiv MovingSofa.e₁⟫ = 1 := by
    intro t
    rw [LinearIsometryEquiv.inner_map_map, e₁_eq, inner_v_v]
  obtain ⟨sgn, hsgn⟩ : ∃ f : I → ℝ,
      ∀ t, f t = ⟪(m t).linearIsometryEquiv MovingSofa.e₁, v (Θ t)⟫ := ⟨_, fun _ => rfl⟩
  have hdec : ∀ t, (m t).linearIsometryEquiv MovingSofa.e₁ = sgn t • v (Θ t) := by
    intro t
    have h := decomp_u_v (Θ t) ((m t).linearIsometryEquiv MovingSofa.e₁)
    rw [horth t, zero_smul, zero_add, ← hsgn t] at h
    exact h
  have hsq' : ∀ t, sgn t ^ 2 = 1 := by
    intro t
    have h := hnorm t
    rw [hdec t, real_inner_smul_left, real_inner_smul_right, inner_v_v] at h
    nlinarith [h]
  have hcont : Continuous sgn := by
    have : sgn = fun t => ((m t).linearIsometryEquiv MovingSofa.e₁) 0 * (-Real.sin (Θ t))
        + ((m t).linearIsometryEquiv MovingSofa.e₁) 1 * Real.cos (Θ t) := by
      funext t; rw [hsgn t, inner_eq, v_coord_zero, v_coord_one]
    rw [this]
    exact (hw'0.mul (Real.continuous_sin.comp Θ.continuous).neg).add
      (hw'1.mul (Real.continuous_cos.comp Θ.continuous))
  have hzero : sgn 0 = 1 := by
    rw [hsgn 0, hL0, hΘ0, e₁_eq, inner_v_v]
  have hone : ∀ t, sgn t = 1 := by
    intro t
    by_contra hne
    have hneg : sgn t = -1 := by
      have h2 : (sgn t - 1) * (sgn t + 1) = 0 := by linear_combination hsq' t
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact absurd (by linarith : sgn t = 1) hne
      · linarith
    have hIVT := intermediate_value_univ t 0 hcont
    have h0mem : (0 : ℝ) ∈ Icc (sgn t) (sgn 0) := by
      rw [Set.mem_Icc, hneg, hzero]
      constructor <;> norm_num
    obtain ⟨s, hs⟩ := hIVT h0mem
    have := hsq' s
    rw [hs] at this
    norm_num at this
  -- assemble
  refine ⟨fun t => Θ t, Θ.continuous, hΘ0, fun t p => ?_⟩
  rw [apply_eq_linear_add (m t) p, rot_eq_smul]
  congr 1
  conv_lhs => rw [decomp_e p]
  rw [map_add, map_smul, map_smul, hu t, hdec t, hone t, one_smul]

end Sofa
