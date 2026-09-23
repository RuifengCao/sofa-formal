/-
# Sofa/GerverMono.lean — Gerver's sofa is a monotone sofa

The upstream `gerversSofa` touches both outer walls of every hallway of its definition: the
contact points are explicit,

    A(α) = (x(π/2 − α), y(π/2 − α)) on the wall `ca α = 1`,
    C(α) = (4x(0) − 2 − x(α), y(α))  on the wall `cb α = 1`   (`α ∈ [0, π/2]`),

(`x`, `y` are the coordinates of the outer boundary: `r` is its radius of curvature).  Hence its
support function is `h(α) = p₁(α) + 1`, `h(α + π/2) = p₂(α) + 1` (`supportFn_gerver`), its supporting
hallways are the hallways of the definition, and it equals its own monotone hull:
**`gerversSofa` is a monotone sofa of rotation angle `π/2`** (`isMonotoneSofa_gerversSofa`).

* `conv_ineq`: `(x a − x b) sin b + (y a − y b) cos b = ∫_b^a r(t) sin(b − t) dt ≤ 0`: the
  boundary curve lies on the inner side of each of its tangent lines (`r ≥ 0`).
* The cross inequalities (`A` against the walls `cb`, `C` against the walls `ca`) are soft
  (`0 ≤ r ≤ 3/2`, `x(0) ≤ 1/5`).
* The contact points avoid the inner quadrants because they lie high (`y ≥ 9/10`) or far out
  (`x ≥ 2/5`): two small interval checks.

STATUS: [PROOF-C-local] round 38 (2026-09-23, Opus 5.5).
-/
import Sofa.GerverConn
import Sofa.MonoSofa

noncomputable section

open Real Set MeasureTheory intervalIntegral MovingSofa
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

set_option Elab.async false

namespace Sofa.GP

open GC IA
open MovingSofa.GerversSofa (A B φ θ r)

/-! ## `x`, `y` on the whole of `[0, π/2]` -/

lemma r_zero {t : ℝ} (ht : π / 2 - φ < t) : r t = 0 := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  rw [r_def, if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (not_le.2 ht)]

lemma integral_r_mul_zero {f : ℝ → ℝ} {b : ℝ} (hb : π / 2 - φ ≤ b) :
    ∫ t in (π / 2 - φ)..b, r t * f t = 0 := by
  rw [← intervalIntegral.integral_zero (a := π / 2 - φ) (b := b)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le hb] at ht
  rw [r_zero ht.1, zero_mul]

lemma x_of_ge {β : ℝ} (hβ : π / 2 - φ ≤ β) : GerversSofa.x β = 1 := by
  rw [x_eq, integral_r_mul_zero hβ, add_zero]

lemma y_of_ge {β : ℝ} (hβ : π / 2 - φ ≤ β) : GerversSofa.y β = 0 := by
  rw [y_eq, integral_r_mul_zero hβ, neg_zero]

/-- `x a − x b = ∫_b^a r cos`. -/
lemma x_sub (a b : ℝ) : GerversSofa.x a - GerversSofa.x b = ∫ t in b..a, r t * Real.cos t := by
  rw [x_eq, x_eq, ← integral_add_adjacent_intervals (intervalIntegrable_r_mul continuous_cos _ b)
    (intervalIntegrable_r_mul continuous_cos b a)]
  ring

/-- `y a − y b = −∫_b^a r sin`. -/
lemma y_sub (a b : ℝ) : GerversSofa.y a - GerversSofa.y b = -∫ t in b..a, r t * Real.sin t := by
  rw [y_eq, y_eq, ← integral_add_adjacent_intervals (intervalIntegrable_r_mul continuous_sin _ b)
    (intervalIntegrable_r_mul continuous_sin b a)]
  ring

lemma r_sin_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ π) : 0 ≤ r t * Real.sin t :=
  mul_nonneg (r_nonneg_le t).1 (sin_nonneg_of_nonneg_of_le_pi h0 h1)

lemma r_cos_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ π / 2) : 0 ≤ r t * Real.cos t :=
  mul_nonneg (r_nonneg_le t).1 (cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h1⟩)

/-- `x` is increasing on `[0, π/2]`. -/
lemma x_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π / 2) :
    GerversSofa.x a ≤ GerversSofa.x b := by
  have := x_sub b a
  have hi : 0 ≤ ∫ t in a..b, r t * Real.cos t :=
    integral_nonneg hab fun t ht => r_cos_nonneg (ha.trans ht.1) (ht.2.trans hb)
  linarith

/-- `y` is decreasing on `[0, π/2]`. -/
lemma y_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ π / 2) :
    GerversSofa.y b ≤ GerversSofa.y a := by
  have := y_sub b a
  have hi : 0 ≤ ∫ t in a..b, r t * Real.sin t :=
    integral_nonneg hab fun t ht => r_sin_nonneg (ha.trans ht.1) (by linarith [ht.2, Real.pi_pos])
  linarith

lemma x_range {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (π / 2)) :
    GerversSofa.x 0 ≤ GerversSofa.x a ∧ GerversSofa.x a ≤ 1 := by
  obtain ⟨p1, -⟩ := bounds
  refine ⟨x_mono le_rfl ha.1 ha.2, ?_⟩
  calc GerversSofa.x a ≤ GerversSofa.x (π / 2) := x_mono ha.1 ha.2 le_rfl
    _ = 1 := x_of_ge (by linarith)

lemma y_range {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (π / 2)) :
    0 ≤ GerversSofa.y a ∧ GerversSofa.y a ≤ 1 := by
  obtain ⟨p1, -⟩ := bounds
  refine ⟨?_, ?_⟩
  · calc (0 : ℝ) = GerversSofa.y (π / 2) := (y_of_ge (by linarith)).symm
      _ ≤ GerversSofa.y a := y_anti ha.1 ha.2 le_rfl
  · calc GerversSofa.y a ≤ GerversSofa.y 0 := y_anti le_rfl ha.1 ha.2
      _ = 1 := y_zero

/-- `1 − y a ≤ (3/2)(1 − cos a)`. -/
lemma one_sub_y_le {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (π / 2)) :
    1 - GerversSofa.y a ≤ 3 / 2 * (1 - Real.cos a) := by
  have e := y_sub a 0
  rw [y_zero] at e
  have hle : ∫ t in (0 : ℝ)..a, r t * Real.sin t ≤ ∫ t in (0 : ℝ)..a, 3 / 2 * Real.sin t :=
    integral_mono_on ha.1 (intervalIntegrable_r_mul continuous_sin _ _)
      ((by fun_prop : Continuous fun t : ℝ => 3 / 2 * Real.sin t).intervalIntegrable _ _)
      fun t ht => by
        have hs := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, ha.2, Real.pi_pos])
        exact mul_le_mul_of_nonneg_right (r_nonneg_le t).2 hs
  rw [intervalIntegral.integral_const_mul, integral_sin, cos_zero] at hle
  linarith

/-- `p₁` by one formula on `[0, π/2]`. -/
lemma p₁_uniform (γ : ℝ) :
    p₁ γ = GerversSofa.x (π / 2 - γ) * Real.cos γ + GerversSofa.y (π / 2 - γ) * Real.sin γ - 1 := by
  rw [p₁]
  split_ifs with h
  · rw [x_of_ge (by linarith), y_of_ge (by linarith)]; ring
  · rfl

/-- `p₂` by one formula on `[0, π/2]`. -/
lemma p₂_uniform (γ : ℝ) :
    p₂ γ = GerversSofa.y γ * Real.cos γ - (4 * GerversSofa.x 0 - 2 - GerversSofa.x γ) * Real.sin γ
      - 1 := by
  rw [p₂]
  split_ifs with h
  · rfl
  · push Not at h
    rw [x_of_ge h.le, y_of_ge h.le]; ring

/-! ## The boundary curve is convex -/

/-- **Convexity of the boundary curve**: `(x a − x b) sin b + (y a − y b) cos b ≤ 0`. -/
lemma conv_ineq {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) (π / 2)) (hb : b ∈ Icc (0 : ℝ) (π / 2)) :
    (GerversSofa.x a - GerversSofa.x b) * Real.sin b
      + (GerversSofa.y a - GerversSofa.y b) * Real.cos b ≤ 0 := by
  have hpi := Real.pi_pos
  have e : (GerversSofa.x a - GerversSofa.x b) * Real.sin b
      + (GerversSofa.y a - GerversSofa.y b) * Real.cos b
        = ∫ t in b..a, r t * Real.sin (b - t) := by
    rw [x_sub, y_sub, ← intervalIntegral.integral_mul_const, neg_mul,
      ← intervalIntegral.integral_mul_const, ← sub_eq_add_neg, ← intervalIntegral.integral_sub
        ((intervalIntegrable_r_mul continuous_cos b a).mul_const _)
        ((intervalIntegrable_r_mul continuous_sin b a).mul_const _)]
    refine integral_congr fun t _ => ?_
    simp only [Real.sin_sub]; ring
  rw [e]
  rcases le_total b a with h | h
  · have hn : ∫ t in b..a, r t * Real.sin (b - t) = -∫ t in b..a, r t * Real.sin (t - b) := by
      rw [← intervalIntegral.integral_neg]
      refine integral_congr fun t _ => ?_
      simp only [show b - t = -(t - b) by ring, Real.sin_neg, mul_neg]
    rw [hn, neg_nonpos]
    exact integral_nonneg h fun t ht => mul_nonneg (r_nonneg_le t).1
      (sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2, ha.2, hb.1]))
  · rw [integral_symm, neg_nonpos]
    exact integral_nonneg h fun t ht => mul_nonneg (r_nonneg_le t).1
      (sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.2]) (by linarith [ht.1, ha.1, hb.2]))

lemma one_sub_cos_le_sin {γ : ℝ} (hγ : γ ∈ Icc (0 : ℝ) (π / 2)) :
    1 - Real.cos γ ≤ Real.sin γ := by
  obtain ⟨hs, hc⟩ := sin_cos_nonneg hγ.1 hγ.2
  have := Real.sin_sq_add_cos_sq γ
  nlinarith [mul_nonneg hs hc]

lemma one_sub_sin_le_cos {γ : ℝ} (hγ : γ ∈ Icc (0 : ℝ) (π / 2)) :
    1 - Real.sin γ ≤ Real.cos γ := by
  obtain ⟨hs, hc⟩ := sin_cos_nonneg hγ.1 hγ.2
  have := Real.sin_sq_add_cos_sq γ
  nlinarith [mul_nonneg hs hc]

/-! ## The contact points -/

/-- The contact point with the outer wall `a`: `A(α) = (x(π/2 − α), y(π/2 − α))`. -/
def ptA (α : ℝ) : ℝ² := pt (GerversSofa.x (π / 2 - α)) (GerversSofa.y (π / 2 - α))

/-- The contact point with the outer wall `c`: `C(α) = (4x(0) − 2 − x(α), y(α))`. -/
def ptC (α : ℝ) : ℝ² := pt (4 * GerversSofa.x 0 - 2 - GerversSofa.x α) (GerversSofa.y α)

lemma ca_ptA (α : ℝ) : ca α (ptA α) = 1 := by
  rw [ptA, ca_pt, p₁_uniform α]; ring

lemma cb_ptC (α : ℝ) : cb α (ptC α) = 1 := by
  rw [ptC, cb_pt, p₂_uniform α]; ring

lemma reflect_mem {γ : ℝ} (hγ : γ ∈ Icc (0 : ℝ) (π / 2)) : π / 2 - γ ∈ Icc (0 : ℝ) (π / 2) :=
  ⟨by linarith [hγ.2], by linarith [hγ.1]⟩

lemma ca_ptA_le {α γ : ℝ} (hα : α ∈ Icc (0 : ℝ) (π / 2)) (hγ : γ ∈ Icc (0 : ℝ) (π / 2)) :
    ca γ (ptA α) ≤ 1 := by
  have h := conv_ineq (reflect_mem hα) (reflect_mem hγ)
  rw [sin_pi_div_two_sub, cos_pi_div_two_sub] at h
  rw [ptA, ca_pt, p₁_uniform γ]
  linarith

lemma cb_ptC_le {α γ : ℝ} (hα : α ∈ Icc (0 : ℝ) (π / 2)) (hγ : γ ∈ Icc (0 : ℝ) (π / 2)) :
    cb γ (ptC α) ≤ 1 := by
  have h := conv_ineq hα hγ
  rw [ptC, cb_pt, p₂_uniform γ]
  linarith

lemma cb_ptA_le {α γ : ℝ} (hα : α ∈ Icc (0 : ℝ) (π / 2)) (hγ : γ ∈ Icc (0 : ℝ) (π / 2)) :
    cb γ (ptA α) ≤ 1 := by
  obtain ⟨hs, hc⟩ := sin_cos_nonneg hγ.1 hγ.2
  obtain ⟨xa0, -⟩ := x_range (reflect_mem hα)
  obtain ⟨xg0, -⟩ := x_range hγ
  obtain ⟨-, ya1⟩ := y_range (reflect_mem hα)
  obtain ⟨yg0, yg1⟩ := y_range hγ
  obtain ⟨-, x02⟩ := x0_bounds
  have h1 := one_sub_y_le hγ
  have h2 := one_sub_cos_le_sin hγ
  have hc1 := Real.cos_le_one γ
  rw [ptA, cb_pt, p₂_uniform γ]
  have k1 : (GerversSofa.y (π / 2 - α) - GerversSofa.y γ) * Real.cos γ
      ≤ (1 - GerversSofa.y γ) * 1 :=
    mul_le_mul (by linarith) hc1 hc (by linarith)
  have k2 : (2 - 2 * GerversSofa.x 0) * Real.sin γ ≤
      (GerversSofa.x (π / 2 - α) + GerversSofa.x γ - 4 * GerversSofa.x 0 + 2) * Real.sin γ :=
    mul_le_mul_of_nonneg_right (by linarith) hs
  nlinarith

lemma ca_ptC_le {α γ : ℝ} (hα : α ∈ Icc (0 : ℝ) (π / 2)) (hγ : γ ∈ Icc (0 : ℝ) (π / 2)) :
    ca γ (ptC α) ≤ 1 := by
  obtain ⟨hs, hc⟩ := sin_cos_nonneg hγ.1 hγ.2
  obtain ⟨xa0, -⟩ := x_range hα
  obtain ⟨xb0, -⟩ := x_range (reflect_mem hγ)
  obtain ⟨-, ya1⟩ := y_range hα
  obtain ⟨yb0, yb1⟩ := y_range (reflect_mem hγ)
  obtain ⟨-, x02⟩ := x0_bounds
  have h1 := one_sub_y_le (reflect_mem hγ)
  rw [cos_pi_div_two_sub] at h1
  have h2 := one_sub_sin_le_cos hγ
  have hs1 := Real.sin_le_one γ
  rw [ptC, ca_pt, p₁_uniform γ]
  have k1 : (GerversSofa.y α - GerversSofa.y (π / 2 - γ)) * Real.sin γ
      ≤ (1 - GerversSofa.y (π / 2 - γ)) * 1 :=
    mul_le_mul (by linarith) hs1 hs (by linarith)
  have k2 : (4 * GerversSofa.x 0 - 2 - GerversSofa.x α - GerversSofa.x (π / 2 - γ)) * Real.cos γ
      ≤ (2 * GerversSofa.x 0 - 2) * Real.cos γ :=
    mul_le_mul_of_nonneg_right (by linarith) hc
  nlinarith

/-! ## The contact points are in the sofa -/

/-- `y` and `x` at `α` on the pieces, as expressions. -/
def yAE : ℕ → IE
  | 0 => yCE 0 eα esα ecα
  | 1 => yCE 1 eα esα ecα
  | 2 => yCE 2 eα esα ecα
  | 3 => yCE 3 eα esα ecα
  | _ => k 0

def xAE : ℕ → IE
  | 0 => xCE 0 eα esα ecα
  | 1 => xCE 1 eα esα ecα
  | 2 => xCE 2 eα esα ecα
  | 3 => xCE 3 eα esα ecα
  | _ => k 1

lemma yAE_eval {j : ℕ} (hj : j ≤ 4) {a : ℝ} (ha : a ∈ Icc (brk j) (brk (j + 1))) :
    (yAE j).eval (envA a) = GerversSofa.y a := by
  rcases Nat.lt_or_ge j 4 with h4 | h4
  · rw [y_eq_yC (by omega) ha]
    interval_cases j <;> simp only [yAE] <;> rw [yCE_eval a _ (by norm_num)] <;> rfl
  · obtain rfl : j = 4 := le_antisymm hj h4
    rw [y_of_ge ha.1]; simp [yAE, k]

lemma xAE_eval {j : ℕ} (hj : j ≤ 4) {a : ℝ} (ha : a ∈ Icc (brk j) (brk (j + 1))) :
    (xAE j).eval (envA a) = GerversSofa.x a := by
  rcases Nat.lt_or_ge j 4 with h4 | h4
  · rw [x_eq_xC (by omega) ha]
    interval_cases j <;> simp only [xAE] <;> rw [xCE_eval a _ (by norm_num)] <;> rfl
  · obtain rfl : j = 4 := le_antisymm hj h4
    rw [x_of_ge ha.1]; simp [xAE, k]

def yHighE (j : ℕ) : IE := k (9 / 10) - yAE j

def xFarE (j : ℕ) : IE := k (2 / 5) - xAE j

/-- `y > 9/10` on `[0, 9/20]`. -/
theorem ck_yHigh : chkA yHighE 14 0 (qup (9 / 20)) = true := by
  decide +kernel

/-- `x > 2/5` on `[9/20, π/2]`. -/
theorem ck_xFar : chkA xFarE 14 (qdn (9 / 20)) topA = true := by
  decide +kernel

/-- On `[0, π/2]`, the boundary point `(x a, y a)` is high (`y > 9/10`) or far (`x > 2/5`). -/
lemma high_or_far {a : ℝ} (ha : a ∈ Icc (0 : ℝ) (π / 2)) :
    9 / 10 < GerversSofa.y a ∨ 2 / 5 < GerversSofa.x a := by
  rcases le_total a (9 / 20) with h | h
  · left
    obtain ⟨j, hj, haj, hc⟩ := of_chkA ck_yHigh ha (by simpa using ha.1)
      (h.trans (by have := le_qup (9 / 20 : ℚ); push_cast at this; exact this))
    simp only [yHighE, IE.eval_sub', k, IE.eval_c, yAE_eval (by omega) haj] at hc
    push_cast at hc
    linarith
  · right
    obtain ⟨j, hj, haj, hc⟩ := of_chkA ck_xFar ha
      ((show ((qdn (9 / 20) : ℤ) : ℝ) / S ≤ 9 / 20 by
        have := qdn_le (9 / 20 : ℚ); push_cast at this; exact this).trans h) (mem_top ha).2
    simp only [xFarE, IE.eval_sub', k, IE.eval_c, xAE_eval (by omega) haj] at hc
    push_cast at hc
    linarith

lemma ptA_mem_Cvx {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (π / 2)) : ptA α ∈ Cvx := by
  obtain ⟨xa0, xa1⟩ := x_range (reflect_mem hα)
  obtain ⟨ya0, ya1⟩ := y_range (reflect_mem hα)
  obtain ⟨x01, x02⟩ := x0_bounds
  refine mem_Cvx.2 ⟨⟨by rw [ptA, pt_zero]; exact xa1, by rw [ptA, pt_one]; exact ya0,
    by rw [ptA, pt_one]; exact ya1⟩, by rw [ptA, pt_zero]; linarith,
    fun γ hγ => ⟨ca_ptA_le hα hγ, cb_ptA_le hα hγ⟩⟩

lemma ptC_mem_Cvx {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (π / 2)) : ptC α ∈ Cvx := by
  obtain ⟨xa0, xa1⟩ := x_range hα
  obtain ⟨ya0, ya1⟩ := y_range hα
  obtain ⟨x01, x02⟩ := x0_bounds
  refine mem_Cvx.2 ⟨⟨by rw [ptC, pt_zero]; linarith, by rw [ptC, pt_one]; exact ya0,
    by rw [ptC, pt_one]; exact ya1⟩, by rw [ptC, pt_zero]; linarith,
    fun γ hγ => ⟨ca_ptC_le hα hγ, cb_ptC_le hα hγ⟩⟩

/-- The contact point `A(α)` lies in the sofa. -/
lemma ptA_mem {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (π / 2)) : ptA α ∈ gerversSofa := by
  rcases high_or_far (reflect_mem hα) with h | h
  · exact mem_of_high (ptA_mem_Cvx hα) (by rw [ptA, pt_one]; linarith)
  · exact mem_of_right (ptA_mem_Cvx hα) (by rw [ptA, pt_zero]; linarith)

/-- The contact point `C(α)` lies in the sofa. -/
lemma ptC_mem {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (π / 2)) : ptC α ∈ gerversSofa := by
  obtain ⟨-, x02⟩ := x0_bounds
  rcases high_or_far hα with h | h
  · exact mem_of_high (ptC_mem_Cvx hα) (by rw [ptC, pt_one]; linarith)
  · exact mem_of_left (ptC_mem_Cvx hα) (by rw [ptC, pt_zero]; linarith)

/-! ## The support function and the supporting hallways -/

lemma isCompact_gerversSofa : IsCompact gerversSofa := by
  have hK : IsCompact ((fun ab : ℝ × ℝ => pt ab.1 ab.2) ''
      (Icc (4 * GerversSofa.x 0 - 3) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image continuous_pt
  refine Metric.isCompact_of_isClosed_isBounded isClosed_gerversSofa (hK.isBounded.subset ?_)
  intro z hz
  obtain ⟨⟨h0, h1, h2⟩, h3, -⟩ := mem_Cvx.1 (mem_gerversSofa_iff.1 hz).1
  exact ⟨(z 0, z 1), ⟨⟨h3, h0⟩, ⟨h1, h2⟩⟩, (eq_pt z).symm⟩

lemma gerversSofa_nonempty : gerversSofa.Nonempty := ⟨_, ptA_mem ⟨le_rfl, by positivity⟩⟩

/-- **The support function of Gerver's sofa** in the directions `u_α`, `α ∈ [0, π/2]`. -/
theorem supportFn_gerver {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (π / 2)) :
    supportFn gerversSofa α = p₁ α + 1 := by
  refine le_antisymm ((supportFn_le_iff isCompact_gerversSofa gerversSofa_nonempty α _).2
    fun z hz => ?_) ?_
  · have := ((mem_Cvx.1 (mem_gerversSofa_iff.1 hz).1).2.2 α hα).1
    rw [ca] at this; linarith
  · have h := le_supportFn isCompact_gerversSofa (ptA_mem hα) α
    have e := ca_ptA α
    rw [ca] at e
    linarith

/-- **The support function of Gerver's sofa** in the directions `v_α`, `α ∈ [0, π/2]`. -/
theorem supportFn_gerver' {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (π / 2)) :
    supportFn gerversSofa (α + π / 2) = p₂ α + 1 := by
  refine le_antisymm ((supportFn_le_iff isCompact_gerversSofa gerversSofa_nonempty _ _).2
    fun z hz => ?_) ?_
  · have := ((mem_Cvx.1 (mem_gerversSofa_iff.1 hz).1).2.2 α hα).2
    rw [cb] at this; rw [u_add_pi_div_two]; linarith
  · have h := le_supportFn isCompact_gerversSofa (ptC_mem hα) (α + π / 2)
    have e := cb_ptC α
    rw [cb] at e
    rw [u_add_pi_div_two] at h
    linarith

/-- The supporting hallways of Gerver's sofa are the hallways of its definition. -/
theorem suppHallway_gerver {α : ℝ} (hα : α ∈ Icc (0 : ℝ) (π / 2)) :
    suppHallway gerversSofa α = rotateTranslate (α : Real.Angle) (GerversSofa.p α) '' hallway := by
  ext z
  rw [suppHallway_eq, mem_L_iff, mem_sdiff, mem_QplusS_iff, mem_QminusS_iff, supportFn_gerver hα,
    supportFn_gerver' hα, u_add_pi_div_two]
  simp only [ca, cb]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by linarith, by linarith⟩, fun ⟨k1, k2⟩ => h3 ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by linarith, by linarith⟩, fun ⟨k1, k2⟩ => h3 ⟨by linarith, by linarith⟩⟩

/-- **Gerver's sofa is its own monotone hull.** -/
theorem Imono_gerver : Imono gerversSofa (π / 2) = gerversSofa := by
  have hpi := Real.pi_pos
  ext z
  rw [mem_Imono_iff, mem_gerversSofa_iff]
  have hL : (∀ t ∈ Icc (0 : ℝ) (π / 2), z ∈ suppHallway gerversSofa t) ↔
      ∀ t ∈ Icc (0 : ℝ) (π / 2), (ca t z ≤ 1 ∧ cb t z ≤ 1) ∧ ¬(ca t z < 0 ∧ cb t z < 0) := by
    refine forall₂_congr fun t ht => ?_
    rw [suppHallway_gerver ht, mem_L_iff]
  rw [hL]
  have hpara : z ∈ para (π / 2) ↔ 0 ≤ z 1 ∧ z 1 ≤ 1 := by
    simp only [para, Hstrip, Vstrip, mem_inter_iff, mem_ofPred_eq, inner_u_pi_div_two]
    tauto
  rw [hpara]
  have h0 : ca 0 z = z 0 := by
    rw [ca_eq, p₁, if_pos (show (0 : ℝ) ≤ φ by linarith [bounds.1])]; simp
  have h1 : cb (π / 2) z = -z 0 - (2 - 4 * GerversSofa.x 0) := by
    rw [cb_eq, Real.sin_pi_div_two, Real.cos_pi_div_two, p_half.2]; ring
  constructor
  · rintro ⟨⟨hz1, hz2⟩, h⟩
    have k0 := (h 0 ⟨le_rfl, by positivity⟩).1.1
    have k1 := (h (π / 2) ⟨by positivity, le_rfl⟩).1.2
    rw [h0] at k0
    rw [h1] at k1
    exact ⟨mem_Cvx.2 ⟨⟨k0, hz1, hz2⟩, by linarith, fun t ht => (h t ht).1⟩, fun t ht => (h t ht).2⟩
  · rintro ⟨hC, h⟩
    obtain ⟨⟨-, hz1, hz2⟩, -, h2⟩ := mem_Cvx.1 hC
    exact ⟨⟨hz1, hz2⟩, fun t ht => ⟨h2 t ht, h t ht⟩⟩

lemma rot_zero_vec (t : ℝ) : rot t 0 = 0 := by
  ext i; fin_cases i <;> simp

/-- Gerver's sofa turns clockwise by `π/2` (Baek's `IsSofaWithAngle`). -/
theorem isSofaWithAngle_gerver : IsSofaWithAngle gerversSofa (π / 2) := by
  refine ⟨0, gmotion, fun τ => -ang τ, by rw [tr_zero]; exact
    isMovingSofa_gerversSofa_of_isConnected isConnected_gerversSofa, continuous_ang.neg,
    by simp [ang], fun τ z => ?_, by simp [ang]⟩
  rw [gmotion_apply, gmotion_apply, rot_zero_vec, zero_sub, sub_eq_add_neg]

/-- Gerver's sofa is in standard position: `h(π/2) = 1`. -/
theorem stdPos_gerver : StdPos gerversSofa (π / 2) := by
  have hpi := Real.pi_pos
  have h := supportFn_gerver (α := π / 2) ⟨by positivity, le_rfl⟩
  rw [p_half.1, zero_add] at h
  exact ⟨h, h⟩

/-- **Gerver's sofa is a monotone sofa of rotation angle `π/2`.** -/
theorem isMonotoneSofa_gerversSofa : IsMonotoneSofa gerversSofa (π / 2) :=
  ⟨gerversSofa, isSofaWithAngle_gerver, stdPos_gerver, Imono_gerver.symm⟩

end Sofa.GP
