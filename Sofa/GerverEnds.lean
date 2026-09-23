/-
# Sofa/GerverEnds.lean — the end points of the tails of Gerver's niche

The tails `B = p₁ u + p₁' v`, `D = −p₂' u + p₂ v` (`Sofa/GerverRomik.lean`) close up with the core
curve of inner corners (Baek Thm 8.4.1 (2)):

    B(π/2 − θ) = x_K(φ),   D(θ) = x_K(π/2 − φ)             (Bg_start, Dg_end).

Both are identities between the closed forms of `x`, `y` at the break points (`GerverClosed.lean`).
Their components along `u_φ`, `v_φ` (resp. `u_{π/2−φ}`, `v_{π/2−φ}`) are linear combinations of
Romik's equations `E₁`, `E₂`, `E₄` and of `sin² + cos² = 1` for `φ` and `θ` (certificates found
with sympy, checked here by `linear_combination`).

STATUS: [PROOF-C] round 39 (2026-09-23, Opus 5.5).
-/
import Sofa.GerverRomik

noncomputable section

open Real Set MovingSofa
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa.GP

open GC IA
open MovingSofa.GerversSofa (A B φ θ r)

/-- A vector is determined by its components along an orthonormal frame `(c, s)`, `(−s, c)`. -/
lemma vec_eq_of_proj {a b : ℝ²} (c s : ℝ) (hcs : s ^ 2 + c ^ 2 = 1)
    (h1 : (a 0 - b 0) * c + (a 1 - b 1) * s = 0)
    (h2 : -(a 0 - b 0) * s + (a 1 - b 1) * c = 0) : a = b := by
  refine ext_two ?_ ?_
  · linear_combination c * h1 - s * h2 - (a 0 - b 0) * hcs
  · linear_combination s * h1 + c * h2 - (a 1 - b 1) * hcs

lemma x_θ_eq : GerversSofa.x θ = xC 1 θ (sin θ) (cos θ) :=
  x_eq_xC (k := 1) (by norm_num) ⟨(brk_mono).2.1.le, le_rfl⟩

lemma y_θ_eq : GerversSofa.y θ = yC 1 θ (sin θ) (cos θ) :=
  y_eq_yC (k := 1) (by norm_num) ⟨(brk_mono).2.1.le, le_rfl⟩

lemma x_φ_eq : GerversSofa.x φ = xC 0 φ (sin φ) (cos φ) :=
  x_eq_xC (k := 0) (by norm_num) ⟨(brk_mono).1.le, le_rfl⟩

lemma y_φ_eq : GerversSofa.y φ = yC 0 φ (sin φ) (cos φ) :=
  y_eq_yC (k := 0) (by norm_num) ⟨(brk_mono).1.le, le_rfl⟩

/-- **The tail `B` starts at the inner corner `x_K(φ)`.** -/
theorem Bg_start : Bg (π / 2 - θ) = innerCorner Kg φ := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  obtain ⟨-, -, -, -, -, e1, e2, -, e4⟩ := gerver_spec
  rw [innerCorner_Kg ⟨by linarith, by linarith⟩, Bg, p₁_uniform, p₁_uniform, dp₁, p₂_uniform,
    sub_sub_cancel, x_of_ge le_rfl, y_of_ge le_rfl, cos_pi_div_two_sub, sin_pi_div_two_sub]
  refine vec_eq_of_proj (cos φ) (sin φ) (sin_sq_add_cos_sq φ) ?_ ?_ <;>
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, u_coord_zero, u_coord_one,
      v_coord_zero, v_coord_one, cos_pi_div_two_sub, sin_pi_div_two_sub] <;>
  rw [x_θ_eq, y_θ_eq, x_φ_eq, y_φ_eq, x_zero_eq] <;>
  simp only [yC, xC, x0C, Fs, Fc, tailY, tailX, SY, SX, brk, ra, rb, rc, Nat.reduceAdd,
      sin_pi_div_two_sub, cos_pi_div_two_sub]
  · linear_combination (sin φ / 2) * e1 + (cos φ / 2) * e2 + (-cos φ * cos θ - sin φ * sin θ) * e4 +
      (1 / 2 + B - cos φ - cos θ ^ 2 / 2 - sin θ ^ 2 / 2 - B * cos θ ^ 2 - B * sin θ ^ 2) *
      sin_sq_add_cos_sq φ + (-1 / 2 + cos φ - B + cos θ * sin φ / 2 - cos φ * sin θ / 2 - sin φ *
      sin θ / 2 + 3 * cos φ * cos θ / 2 + B * cos φ * cos θ + B * sin φ * sin θ + A * cos θ * sin φ
      / 2 + cos φ * cos θ * θ / 2 + cos θ * sin φ * θ / 2 + sin φ * sin θ * θ / 2 - A * cos φ * cos
      θ - A * sin φ * sin θ - 3 * cos φ * φ * sin θ / 2 - cos φ * cos θ * π / 2 - cos θ * φ * sin φ
      / 2 - π * sin φ * sin θ / 2 - cos φ * cos θ * φ ^ 2 / 4 - cos φ * cos θ * θ ^ 2 / 4 - sin φ *
      sin θ * φ ^ 2 / 4 - sin φ * sin θ * θ ^ 2 / 4 + 3 * A * cos φ * sin θ / 2 + 3 * cos φ * cos θ
      * φ / 2 + 3 * cos φ * sin θ * θ / 2 + 3 * φ * sin φ * sin θ / 2 + A * cos φ * cos θ * φ / 2 +
      A * φ * sin φ * sin θ / 2 + cos φ * cos θ * φ * θ / 2 + φ * sin φ * sin θ * θ / 2 - A * cos φ
      * cos θ * θ / 2 - A * sin φ * sin θ * θ / 2) * sin_sq_add_cos_sq θ
  · linear_combination (cos φ / 2) * e1 + (sin φ / 2) * e2 + (-2 * cos θ * sin φ) * e4 + (-1 / 2 +
      sin φ + cos θ ^ 2 / 2 + sin θ ^ 2 / 2 - cos φ ^ 2 - 2 * sin φ ^ 2 - A / 2 + cos φ * sin φ + A
      * cos θ ^ 2 / 2 + A * sin θ ^ 2 / 2 - A * cos φ ^ 2 - 3 * sin φ * sin θ + 3 * cos θ * sin φ +
      A * cos φ * sin θ + cos φ * π * sin θ / 2 - B * cos φ * sin θ - 3 * A * cos θ * sin φ - 3 * φ
      * sin φ * sin θ - 2 * B * cos φ * sin φ + 3 * A * sin φ * sin θ + 3 * B * cos θ * sin φ + 3 *
      sin φ * sin θ * θ - 3 * cos φ * φ * sin θ / 2 - 3 * cos θ * π * sin φ / 2 - 3 * cos θ * sin φ
      * φ ^ 2 / 4 - 3 * cos θ * sin φ * θ ^ 2 / 4 - cos φ * sin θ * θ / 2 + cos φ * sin θ * φ ^ 2 /
      4 + cos φ * sin θ * θ ^ 2 / 4 + 3 * cos θ * sin φ * θ / 2 + 9 * cos θ * φ * sin φ / 2 + A *
      cos φ * sin θ * θ / 2 - 3 * A * cos θ * sin φ * θ / 2 - A * cos φ * φ * sin θ / 2 - cos φ * φ
      * sin θ * θ / 2 + 3 * A * cos θ * φ * sin φ / 2 + 3 * cos θ * φ * sin φ * θ / 2) *
      sin_sq_add_cos_sq φ + (1 / 2 + A / 2 - sin φ + cos φ * cos θ / 2 + sin φ * sin θ / 2 - 3 * cos
      θ * sin φ / 2 - cos φ * sin θ / 2 + A * cos θ * sin φ + B * cos φ * sin θ + A * cos φ * cos θ
      / 2 + cos φ * cos θ * θ / 2 + cos φ * sin θ * θ / 2 + cos θ * π * sin φ / 2 - A * cos φ * sin
      θ - B * cos θ * sin φ - 3 * A * sin φ * sin θ / 2 - 3 * cos θ * φ * sin φ / 2 - 3 * sin φ *
      sin θ * θ / 2 - cos φ * cos θ * φ / 2 - cos φ * π * sin θ / 2 - cos θ * sin φ * θ / 2 - cos φ
      * sin θ * φ ^ 2 / 4 - cos φ * sin θ * θ ^ 2 / 4 + cos θ * sin φ * φ ^ 2 / 4 + cos θ * sin φ *
      θ ^ 2 / 4 + 3 * cos φ * φ * sin θ / 2 + 3 * φ * sin φ * sin θ / 2 + A * cos φ * φ * sin θ / 2
      + A * cos θ * sin φ * θ / 2 + cos φ * φ * sin θ * θ / 2 - A * cos φ * sin θ * θ / 2 - A * cos
      θ * φ * sin φ / 2 - cos θ * φ * sin φ * θ / 2) * sin_sq_add_cos_sq θ

/-- **The tail `D` ends at the inner corner `x_K(π/2 − φ)`.** -/
theorem Dg_end : Dg θ = innerCorner Kg (π / 2 - φ) := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  obtain ⟨-, -, -, -, -, e1, e2, -, e4⟩ := gerver_spec
  rw [innerCorner_Kg ⟨by linarith, by linarith⟩, Dg, p₁_uniform, p₂_uniform, dp₂, p₂_uniform,
    sub_sub_cancel, x_of_ge le_rfl, y_of_ge le_rfl, cos_pi_div_two_sub, sin_pi_div_two_sub]
  have hcs : cos φ ^ 2 + sin φ ^ 2 = 1 := cos_sq_add_sin_sq φ
  refine vec_eq_of_proj (sin φ) (cos φ) hcs ?_ ?_ <;>
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, u_coord_zero, u_coord_one,
      v_coord_zero, v_coord_one, cos_pi_div_two_sub, sin_pi_div_two_sub] <;>
  rw [x_θ_eq, y_θ_eq, x_φ_eq, y_φ_eq, x_zero_eq] <;>
  simp only [yC, xC, x0C, Fs, Fc, tailY, tailX, SY, SX, brk, ra, rb, rc, Nat.reduceAdd,
      sin_pi_div_two_sub, cos_pi_div_two_sub]
  · linear_combination (cos φ / 2) * e1 + (sin φ / 2) * e2 + (-2 * cos θ * sin φ) * e4 + (3 / 2 -
      sin φ - cos φ ^ 2 - 3 * cos θ ^ 2 / 2 - 3 * sin θ ^ 2 / 2 - A / 2 + cos φ * sin φ + sin φ *
      sin θ + A * cos θ ^ 2 / 2 + A * sin θ ^ 2 / 2 - A * cos φ ^ 2 - cos θ * sin φ + A * cos φ *
      sin θ + A * cos θ * sin φ + φ * sin φ * sin θ + cos φ * π * sin θ / 2 + cos θ * π * sin φ / 2
      - A * sin φ * sin θ - B * cos φ * sin θ - B * cos θ * sin φ - sin φ * sin θ * θ + 2 * B * cos
      φ * sin φ - 3 * cos φ * φ * sin θ / 2 - 3 * cos θ * φ * sin φ / 2 - cos φ * sin θ * θ / 2 -
      cos θ * sin φ * θ / 2 + cos φ * sin θ * φ ^ 2 / 4 + cos φ * sin θ * θ ^ 2 / 4 + cos θ * sin φ
      * φ ^ 2 / 4 + cos θ * sin φ * θ ^ 2 / 4 + A * cos φ * sin θ * θ / 2 + A * cos θ * sin φ * θ /
      2 - A * cos φ * φ * sin θ / 2 - A * cos θ * φ * sin φ / 2 - cos φ * φ * sin θ * θ / 2 - cos θ
      * φ * sin φ * θ / 2) * sin_sq_add_cos_sq φ + (-3 / 2 + sin φ + A / 2 + 2 * cos φ ^ 2 + cos φ *
      cos θ / 2 - 7 * sin φ * sin θ / 2 - cos φ * sin θ / 2 + 5 * cos θ * sin φ / 2 + B * cos φ *
      sin θ + A * cos φ * cos θ / 2 + cos φ * cos θ * θ / 2 + cos φ * sin θ * θ / 2 - A * cos φ *
      sin θ - 4 * B * cos φ * sin φ - 3 * A * cos θ * sin φ + 3 * B * cos θ * sin φ - 5 * φ * sin φ
      * sin θ / 2 - 3 * cos θ * π * sin φ / 2 - 3 * cos θ * sin φ * φ ^ 2 / 4 - 3 * cos θ * sin φ *
      θ ^ 2 / 4 - cos φ * cos θ * φ / 2 - cos φ * π * sin θ / 2 - cos φ * sin θ * φ ^ 2 / 4 - cos φ
      * sin θ * θ ^ 2 / 4 + 3 * cos φ * φ * sin θ / 2 + 3 * cos θ * sin φ * θ / 2 + 5 * A * sin φ *
      sin θ / 2 + 5 * sin φ * sin θ * θ / 2 + 9 * cos θ * φ * sin φ / 2 + A * cos φ * φ * sin θ / 2
      + cos φ * φ * sin θ * θ / 2 - 3 * A * cos θ * sin φ * θ / 2 - A * cos φ * sin θ * θ / 2 + 3 *
      A * cos θ * φ * sin φ / 2 + 3 * cos θ * φ * sin φ * θ / 2) * sin_sq_add_cos_sq θ
  · linear_combination (sin φ / 2) * e1 + (cos φ / 2) * e2 + (-cos φ * cos θ - sin φ * sin θ) * e4 +
      (1 / 2 + B + cos φ - cos θ ^ 2 / 2 - sin θ ^ 2 / 2 - B * cos θ ^ 2 - B * sin θ ^ 2 - 4 * B *
      cos φ ^ 2 - 4 * cos φ * sin θ - 2 * cos φ * sin φ + 4 * cos φ * cos θ - cos φ * cos θ * φ ^ 2
      - cos φ * cos θ * θ ^ 2 - 4 * A * cos φ * cos θ - 4 * cos φ * φ * sin θ - 2 * cos φ * cos θ *
      π + 2 * cos φ * cos θ * θ + 4 * A * cos φ * sin θ + 4 * B * cos φ * cos θ + 4 * cos φ * sin θ
      * θ + 6 * cos φ * cos θ * φ - 2 * A * cos φ * cos θ * θ + 2 * A * cos φ * cos θ * φ + 2 * cos
      φ * cos θ * φ * θ) * sin_sq_add_cos_sq φ + (-1 / 2 - B - cos φ + cos θ * sin φ / 2 + 2 * cos φ
      * sin φ + 4 * B * cos φ ^ 2 - 5 * cos φ * cos θ / 2 - sin φ * sin θ / 2 + 7 * cos φ * sin θ /
      2 + B * sin φ * sin θ + A * cos θ * sin φ / 2 + cos θ * sin φ * θ / 2 + sin φ * sin θ * θ / 2
      - A * sin φ * sin θ - 3 * B * cos φ * cos θ + 3 * A * cos φ * cos θ - 9 * cos φ * cos θ * φ /
      2 - 5 * A * cos φ * sin θ / 2 - 5 * cos φ * sin θ * θ / 2 - 3 * cos φ * cos θ * θ / 2 - cos θ
      * φ * sin φ / 2 - π * sin φ * sin θ / 2 - sin φ * sin θ * φ ^ 2 / 4 - sin φ * sin θ * θ ^ 2 /
      4 + 3 * cos φ * cos θ * π / 2 + 3 * φ * sin φ * sin θ / 2 + 3 * cos φ * cos θ * φ ^ 2 / 4 + 3
      * cos φ * cos θ * θ ^ 2 / 4 + 5 * cos φ * φ * sin θ / 2 + A * φ * sin φ * sin θ / 2 + φ * sin
      φ * sin θ * θ / 2 - 3 * A * cos φ * cos θ * φ / 2 - 3 * cos φ * cos θ * φ * θ / 2 - A * sin φ
      * sin θ * θ / 2 + 3 * A * cos φ * cos θ * θ / 2) * sin_sq_add_cos_sq θ

end Sofa.GP
