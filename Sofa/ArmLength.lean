/-
# Sofa/ArmLength.lean — Baek §6.2: the arm lengths `f^±_K`, `g^±_K`

The supporting hallway `L_K(t)` has outer corner `y_K(t) = h_K(t) u_t + h_K(t+π/2) v_t` and
inner corner `x_K(t) = y_K(t) − u_t − v_t`.  The arm lengths measure how far the contact
vertices are from the outer corner:

    `f^±_K(t) = ⟪y_K(t) − A^±_K(t), v_t⟫`,   `g^±_K(t) = ⟪y_K(t) − C^±_K(t), u_t⟫`,

with `A^±_K(t) = v^±_K(t)` and `C^±_K(t) = v^±_K(t+π/2)` (Def 2.5.1).

Contents: Def 6.2.1, Prop 6.2.1 (`y_K` is on both tangent lines), Prop 6.2.2 (mirror), and
**Lemma 6.2.4** `g⁺_K(t) = ∫_{(t,t+π/2]} sin(s−t) σ_K(ds)`, a direct corollary of Thm 5.2.2.

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.SurfaceThm

noncomputable section

open Real Set Filter Topology MeasureTheory MovingSofa
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²}

/-! ## The moving frame -/

/-- A vector orthogonal to `u_t` is a multiple of `v_t`. -/
lemma eq_smul_v_of_inner_u_eq_zero {p : ℝ²} {t : ℝ} (h : ⟪p, u t⟫ = 0) : p = ⟪p, v t⟫ • v t := by
  conv_lhs => rw [decomp_u_v t p]
  rw [h, zero_smul, zero_add]

/-! ## The corners of the supporting hallway -/

@[simp] lemma inner_outerCorner_u (K : Set ℝ²) (t : ℝ) :
    ⟪outerCorner K t, u t⟫ = supportFn K t := by
  rw [outerCorner, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u,
    inner_v_u]
  ring

@[simp] lemma inner_outerCorner_v (K : Set ℝ²) (t : ℝ) :
    ⟪outerCorner K t, v t⟫ = supportFn K (t + π / 2) := by
  rw [outerCorner, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_v,
    inner_v_v]
  ring

@[simp] lemma inner_outerCorner_u_add (K : Set ℝ²) (t : ℝ) :
    ⟪outerCorner K t, u (t + π / 2)⟫ = supportFn K (t + π / 2) := by
  rw [u_add_pi_div_two, inner_outerCorner_v]

/-! ## Definition 6.2.1: the arm lengths -/

/-- `f⁺_K(t) = ⟪y_K(t) − A⁺_K(t), v_t⟫`. -/
def armFp (K : Set ℝ²) (t : ℝ) : ℝ := ⟪outerCorner K t - vtxP K t, v t⟫

/-- `f⁻_K(t) = ⟪y_K(t) − A⁻_K(t), v_t⟫`. -/
def armFm (K : Set ℝ²) (t : ℝ) : ℝ := ⟪outerCorner K t - vtxM K t, v t⟫

/-- `g⁺_K(t) = ⟪y_K(t) − C⁺_K(t), u_t⟫`. -/
def armGp (K : Set ℝ²) (t : ℝ) : ℝ := ⟪outerCorner K t - vtxP K (t + π / 2), u t⟫

/-- `g⁻_K(t) = ⟪y_K(t) − C⁻_K(t), u_t⟫`. -/
def armGm (K : Set ℝ²) (t : ℝ) : ℝ := ⟪outerCorner K t - vtxM K (t + π / 2), u t⟫

lemma armFp_eq (K : Set ℝ²) (t : ℝ) : armFp K t = supportFn K (t + π / 2) - edgeMax K t := by
  rw [armFp, inner_sub_left, inner_outerCorner_v, inner_vtxP_v]

lemma armFm_eq (K : Set ℝ²) (t : ℝ) : armFm K t = supportFn K (t + π / 2) - edgeMin K t := by
  rw [armFm, inner_sub_left, inner_outerCorner_v, inner_vtxM_v]

/-! ## Proposition 6.2.1 -/

/-- `y_K(t) − A⁺_K(t)` is orthogonal to `u_t` (both points are on the outer wall `a_K(t)`). -/
lemma inner_outerCorner_sub_vtxP_u (K : Set ℝ²) (t : ℝ) :
    ⟪outerCorner K t - vtxP K t, u t⟫ = 0 := by
  rw [inner_sub_left, inner_outerCorner_u, inner_vtxP_u, sub_self]

/-- `y_K(t) − C⁺_K(t)` is orthogonal to `v_t` (both points are on the outer wall `c_K(t)`). -/
lemma inner_outerCorner_sub_vtxP_v (K : Set ℝ²) (t : ℝ) :
    ⟪outerCorner K t - vtxP K (t + π / 2), v t⟫ = 0 := by
  rw [inner_sub_left, inner_outerCorner_v, ← u_add_pi_div_two, inner_vtxP_u, sub_self]

/-- **Proposition 6.2.1** (first half): `y_K(t) = A⁺_K(t) + f⁺_K(t) v_t`. -/
theorem outerCorner_eq_vtxP_add (K : Set ℝ²) (t : ℝ) :
    outerCorner K t = vtxP K t + armFp K t • v t := by
  have h := eq_smul_v_of_inner_u_eq_zero (inner_outerCorner_sub_vtxP_u K t)
  rw [← armFp] at h
  exact sub_eq_iff_eq_add'.1 h

/-- **Proposition 6.2.1** (second half): `y_K(t) = C⁺_K(t) + g⁺_K(t) u_t`. -/
theorem outerCorner_eq_vtxP_add' (K : Set ℝ²) (t : ℝ) :
    outerCorner K t = vtxP K (t + π / 2) + armGp K t • u t := by
  have hp := decomp_u_v t (outerCorner K t - vtxP K (t + π / 2))
  rw [inner_outerCorner_sub_vtxP_v, zero_smul, add_zero, ← armGp] at hp
  exact sub_eq_iff_eq_add'.1 hp

/-! ## Lemma 6.2.4 -/

/-- `−⟪v_s, u_t⟫ = sin(s − t)`. -/
lemma neg_inner_v_u (s t : ℝ) : -⟪v s, u t⟫ = sin (s - t) := by
  simp only [inner_eq, u_coord_zero, u_coord_one, v_coord_zero, v_coord_one]
  rw [sin_sub]
  ring

/-- **Baek Lemma 6.2.4.** `g⁺_K(t) = ∫_{(t, t+π/2]} sin(s − t) σ_K(ds)`. -/
theorem armGp_eq_setIntegral (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    armGp K t = ∫ s in Ioc t (t + π / 2), sin (s - t) ∂(sigmaK K) := by
  -- `g⁺(t) = ⟪A⁺(t) − C⁺(t), u_t⟫ = −⟪v⁺(t+π/2) − v⁺(t), u_t⟫`
  have h1 : armGp K t = -⟪vtxP K (t + π / 2) - vtxP K t, u t⟫ := by
    rw [armGp, inner_sub_left, inner_sub_left, inner_outerCorner_u, inner_vtxP_u]
    ring
  have h2 := inner_vtxP_sub_eq_setIntegral hK hne (u t) (by linarith [pi_pos] : t ≤ t + π / 2)
  rw [h1, h2, ← integral_neg]
  exact setIntegral_congr_fun measurableSet_Ioc fun s _ => neg_inner_v_u s t

/-! ## The fundamental theorem of calculus for `h_K` -/

/-- `edgeMax K` is the difference of a monotone and a continuous function, hence measurable and
interval integrable. -/
lemma edgeMax_eq_arcFn_sub (K : Set ℝ²) (t : ℝ) :
    edgeMax K t = arcFn K t - ∫ s in (0:ℝ)..t, supportFn K s := by
  rw [arcFn, inner_vtxP_v]; ring

lemma intervalIntegrable_edgeMax (hK : IsCompact K) (hne : K.Nonempty) (a b : ℝ) :
    IntervalIntegrable (edgeMax K) volume a b := by
  have he : edgeMax K = fun t => arcFn K t - ∫ s in (0:ℝ)..t, supportFn K s :=
    funext (edgeMax_eq_arcFn_sub K)
  rw [he]
  exact ((arcFn_mono hK hne).intervalIntegrable).sub
    ((continuous_primitive_supportFn hK hne).intervalIntegrable a b)

/-- **FTC for the support function**: `h_K(b) − h_K(a) = ∫_a^b ⟪v⁺_K(s), v_s⟫ ds`. -/
theorem supportFn_sub_eq_intervalIntegral (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ}
    (hab : a ≤ b) : supportFn K b - supportFn K a = ∫ s in a..b, edgeMax K s :=
  (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    ((continuous_supportFn hK hne).continuousOn)
    (fun x _ => hasDerivWithinAt_supportFn_Ioi hK hne x)
    (intervalIntegrable_edgeMax hK hne a b)).symm

/-! ## Theorem 6.2.5 -/

/-- `g⁺_K(t) = h_K(t) + ⟪v⁺_K(t+π/2), v_{t+π/2}⟫`. -/
lemma armGp_eq_add (K : Set ℝ²) (t : ℝ) :
    armGp K t = supportFn K t + edgeMax K (t + π / 2) := by
  rw [armGp, inner_sub_left, inner_outerCorner_u, ← inner_vtxP_v]
  have hv : v (t + π / 2) = -u t := v_add_pi_div_two t
  rw [hv, inner_neg_right]
  ring

/-- **Baek Theorem 6.2.5** (integrated form): `d f⁺_K = g⁺_K dt − σ_K`, i.e.

    `σ_K((a,b]) = ∫_a^b g⁺_K(s) ds − (f⁺_K(b) − f⁺_K(a))`. -/
theorem sigmaK_Ioc_toReal_eq (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ} (hab : a ≤ b) :
    (sigmaK K (Ioc a b)).toReal
      = (∫ s in a..b, armGp K s) - (armFp K b - armFp K a) := by
  have hg : (∫ s in a..b, armGp K s)
      = (∫ s in a..b, supportFn K s) + ∫ s in a..b, edgeMax K (s + π / 2) := by
    have hshiftint : IntervalIntegrable (fun s => edgeMax K (s + π / 2)) volume a b := by
      have h := (intervalIntegrable_edgeMax hK hne (a + π / 2) (b + π / 2)).comp_add_right (π / 2)
      rwa [add_sub_cancel_right, add_sub_cancel_right] at h
    rw [← intervalIntegral.integral_add (integrable_supportFn hK hne a b) hshiftint]
    exact intervalIntegral.integral_congr fun s _ => armGp_eq_add K s
  have hshift : (∫ s in a..b, edgeMax K (s + π / 2))
      = supportFn K (b + π / 2) - supportFn K (a + π / 2) := by
    rw [intervalIntegral.integral_comp_add_right (fun s => edgeMax K s) (π / 2)]
    exact (supportFn_sub_eq_intervalIntegral hK hne (by linarith)).symm
  rw [sigmaK_Ioc_toReal hK hne hab, hg, hshift, armFp_eq, armFp_eq,
    edgeMax_eq_arcFn_sub, edgeMax_eq_arcFn_sub,
    ← intervalIntegral.integral_add_adjacent_intervals (integrable_supportFn hK hne 0 a)
      (integrable_supportFn hK hne a b)]
  ring

/-! ## Theorem 6.2.3: the derivatives of the corners -/

lemma u_eq_pt (t : ℝ) : u t = pt (cos t) (sin t) := by
  ext i; fin_cases i <;> simp [pt, e₀, e₁]

lemma v_eq_pt (t : ℝ) : v t = pt (-sin t) (cos t) := by
  ext i; fin_cases i <;> simp [pt, e₀, e₁]

lemma hasDerivAt_u (t : ℝ) : HasDerivAt u (v t) t := by
  have h : HasDerivAt (fun s : ℝ => cos s • e₀ + sin s • e₁) (-sin t • e₀ + cos t • e₁) t :=
    ((Real.hasDerivAt_cos t).smul_const e₀).add ((Real.hasDerivAt_sin t).smul_const e₁)
  have e1 : (fun s : ℝ => cos s • e₀ + sin s • e₁) = u := by
    funext s; rw [u_eq_pt, pt]
  have e2 : -sin t • e₀ + cos t • e₁ = v t := by rw [v_eq_pt, pt]
  rwa [e1, e2] at h

lemma hasDerivAt_v (t : ℝ) : HasDerivAt v (-u t) t := by
  have h : HasDerivAt (fun s : ℝ => (-sin s) • e₀ + cos s • e₁) ((-cos t) • e₀ + (-sin t) • e₁) t :=
    (((Real.hasDerivAt_sin t).neg).smul_const e₀).add ((Real.hasDerivAt_cos t).smul_const e₁)
  have e1 : (fun s : ℝ => (-sin s) • e₀ + cos s • e₁) = v := by
    funext s; rw [v_eq_pt, pt]
  have e2 : (-cos t) • e₀ + (-sin t) • e₁ = -u t := by
    rw [u_eq_pt, pt, neg_add, ← neg_smul, ← neg_smul]
  rwa [e1, e2] at h

lemma hasDerivWithinAt_supportFn_shift (hK : IsCompact K) (hne : K.Nonempty) (t c : ℝ) :
    HasDerivWithinAt (fun s => supportFn K (s + c)) (edgeMax K (t + c)) (Ioi t) t := by
  have hinner := (hasDerivWithinAt_supportFn_Ioi hK hne (t + c))
  have hshift : HasDerivWithinAt (fun s : ℝ => s + c) 1 (Ioi t) t :=
    ((hasDerivAt_id t).add_const c).hasDerivWithinAt
  have hmaps : MapsTo (fun s : ℝ => s + c) (Ioi t) (Ioi (t + c)) := fun s hs => by
    simpa using add_lt_add_right hs c
  have h := HasDerivWithinAt.comp t hinner hshift hmaps
  rw [mul_one] at h
  exact h

/-- **Baek Theorem 6.2.3** (outer corner): `y'_K(t) = −f⁺_K(t) u_t + g⁺_K(t) v_t`. -/
theorem hasDerivWithinAt_outerCorner (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    HasDerivWithinAt (outerCorner K) ((-armFp K t) • u t + armGp K t • v t) (Ioi t) t := by
  have h1 : HasDerivWithinAt (fun s => supportFn K s • u s)
      (supportFn K t • v t + edgeMax K t • u t) (Ioi t) t :=
    (hasDerivWithinAt_supportFn_Ioi hK hne t).smul (hasDerivAt_u t).hasDerivWithinAt
  have h2 : HasDerivWithinAt (fun s => supportFn K (s + π / 2) • v s)
      (supportFn K (t + π / 2) • (-u t) + edgeMax K (t + π / 2) • v t) (Ioi t) t :=
    (hasDerivWithinAt_supportFn_shift hK hne t (π / 2)).smul (hasDerivAt_v t).hasDerivWithinAt
  have h := h1.add h2
  have e1 : ((fun s => supportFn K s • u s) + fun s => supportFn K (s + π / 2) • v s)
      = outerCorner K := by
    funext s; simp only [Pi.add_apply]; rw [outerCorner]
  have e2 : supportFn K t • v t + edgeMax K t • u t
      + (supportFn K (t + π / 2) • (-u t) + edgeMax K (t + π / 2) • v t)
      = (-armFp K t) • u t + armGp K t • v t := by
    rw [armFp_eq, armGp_eq_add]
    module
  rwa [e1, e2] at h

/-- **Baek Theorem 6.2.3** (inner corner): `x'_K(t) = (1 − f⁺_K(t)) u_t + (g⁺_K(t) − 1) v_t`. -/
theorem hasDerivWithinAt_innerCorner (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    HasDerivWithinAt (innerCorner K) ((1 - armFp K t) • u t + (armGp K t - 1) • v t) (Ioi t) t := by
  have h := ((hasDerivWithinAt_outerCorner hK hne t).sub
    (hasDerivAt_u t).hasDerivWithinAt).sub (hasDerivAt_v t).hasDerivWithinAt
  have e1 : (outerCorner K - u - v) = innerCorner K := by
    funext s
    simp only [Pi.sub_apply]
    rw [innerCorner, outerCorner]
    module
  have e2 : (-armFp K t) • u t + armGp K t • v t - v t - -u t
      = (1 - armFp K t) • u t + (armGp K t - 1) • v t := by
    module
  rwa [e1, e2] at h

/-- The injectivity condition (3) of Def 6.1.2 in terms of the arm lengths:
`⟪x'_K(t), u_t⟫ = 1 − f⁺_K(t)` and `⟪x'_K(t), v_t⟫ = g⁺_K(t) − 1`. -/
lemma inner_innerCorner_deriv (K : Set ℝ²) (t : ℝ) :
    ⟪(1 - armFp K t) • u t + (armGp K t - 1) • v t, u t⟫ = 1 - armFp K t ∧
      ⟪(1 - armFp K t) • u t + (armGp K t - 1) • v t, v t⟫ = armGp K t - 1 := by
  constructor
  · rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u, inner_v_u]; ring
  · rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_v, inner_v_v]; ring

end Sofa
