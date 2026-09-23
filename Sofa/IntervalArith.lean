/-
# Sofa/IntervalArith.lean — verified interval arithmetic for numerical certificates

A small, kernel-checkable interval arithmetic, used to certify numerical facts about Gerver's sofa
(its constants `A, B, φ, θ` first).  Everything is proved: a certificate is a Boolean computation
checked by `decide +kernel`, and a soundness theorem turns `true` into a real inequality.  No
`native_decide`, no extra axioms.

* **Alternating Taylor bounds** (`sin_le_sinPoly`, `sinPoly_le_sin`, `cos_le_cosPoly`,
  `cosPoly_le_cos`): for `x ≥ 0` the partial sums of the Taylor series of `sin`, `cos` alternate
  around the function (proved by induction, integrating the previous bound).
* **Fixed-point intervals** `Iv` with integer end points in units of `2⁻⁴⁰`, outward rounding, and
  enclosures of `+, −, ×, sin, cos` (`Iv.mem_add`, …, `Iv.mem_sin`, `Iv.mem_cos`; the last two for
  arguments in `[0, 1]`).
* **Expressions** `IE` (polynomial expressions in variables with rational constants) with their
  interval evaluation and its soundness (`IE.mem_ieval`).
* **Derivatives of expressions** (round 37): forward mode `IE.evalD`, the chain rule along a path of
  environments `IE.hasDerivAt_eval`, and the derivative as an expression `IE.diff` (`IE.eval_diff`),
  so that partial derivatives can be enclosed by the same interval evaluation.

This file imports only Mathlib: the upstream `ABφθSpec.existsUnique` is proved from it
(`Sofa/GerverUnique.lean`).

STATUS: [PROOF-C-local] round 36–37 (2026-09-23, Opus 5.5).
-/
import Mathlib

noncomputable section

open Real Set

namespace Sofa.IA

/-! ## Alternating Taylor bounds for `sin` and `cos` -/

/-- `∑_{j<n} (−1)^j x^{2j+1} / (2j+1)!`. -/
def sinPoly (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (-1) ^ j * x ^ (2 * j + 1) / (2 * j + 1).factorial

/-- `∑_{j<n} (−1)^j x^{2j} / (2j)!`. -/
def cosPoly (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (-1) ^ j * x ^ (2 * j) / (2 * j).factorial

lemma hasDerivAt_sinPoly (n : ℕ) (x : ℝ) : HasDerivAt (sinPoly n) (cosPoly n x) x := by
  have h : ∀ j ∈ Finset.range n, HasDerivAt
      (fun y : ℝ => (-1) ^ j * y ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ))
      ((-1) ^ j * x ^ (2 * j) / ((2 * j).factorial : ℝ)) x := by
    intro j _
    have h1 := ((hasDerivAt_pow (2 * j + 1) x).const_mul ((-1 : ℝ) ^ j)).div_const
      ((2 * j + 1).factorial : ℝ)
    refine h1.congr_deriv ?_
    rw [Nat.add_sub_cancel, Nat.factorial_succ]
    push_cast
    field_simp
  have := HasDerivAt.fun_sum h
  exact this

lemma cosPoly_succ (n : ℕ) (x : ℝ) :
    cosPoly (n + 1) x
      = (∑ i ∈ Finset.range n, (-1) ^ (i + 1) * x ^ (2 * i + 2) / (2 * i + 2).factorial) + 1 := by
  rw [cosPoly, Finset.sum_range_succ']
  simp [mul_add]

lemma hasDerivAt_cosPoly (n : ℕ) (x : ℝ) : HasDerivAt (cosPoly (n + 1)) (-sinPoly n x) x := by
  have e : cosPoly (n + 1) = fun y : ℝ =>
      (∑ i ∈ Finset.range n, (-1) ^ (i + 1) * y ^ (2 * i + 2) / ((2 * i + 2).factorial : ℝ))
        + 1 := by
    funext y; exact cosPoly_succ n y
  rw [e]
  have h : ∀ i ∈ Finset.range n, HasDerivAt
      (fun y : ℝ => (-1) ^ (i + 1) * y ^ (2 * i + 2) / ((2 * i + 2).factorial : ℝ))
      (-((-1) ^ i * x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ))) x := by
    intro i _
    have h1 := ((hasDerivAt_pow (2 * i + 2) x).const_mul ((-1 : ℝ) ^ (i + 1))).div_const
      ((2 * i + 2).factorial : ℝ)
    refine h1.congr_deriv ?_
    rw [show 2 * i + 2 - 1 = 2 * i + 1 by omega, show 2 * i + 2 = (2 * i + 1) + 1 by ring,
      Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have h2 := (HasDerivAt.fun_sum h).add_const 1
  rw [sinPoly, ← Finset.sum_neg_distrib]
  exact h2

lemma sinPoly_zero (n : ℕ) : sinPoly n 0 = 0 := by
  simp [sinPoly]

lemma cosPoly_succ_zero (n : ℕ) : cosPoly (n + 1) 0 = 1 := by
  rw [cosPoly_succ]; simp

/-- A function vanishing at `0` whose derivative is `≤ 0` on `[0, ∞)` is `≤ 0` there. -/
lemma nonpos_of_deriv_nonpos {g g' : ℝ → ℝ} (hg : ∀ y, HasDerivAt g (g' y) y) (h0 : g 0 = 0)
    (hd : ∀ y, 0 ≤ y → g' y ≤ 0) {x : ℝ} (hx : 0 ≤ x) : g x ≤ 0 := by
  have hanti : AntitoneOn g (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun y _ => (hg y).continuousAt.continuousWithinAt)
      (fun y _ => (hg y).differentiableAt.differentiableWithinAt) (fun y hy => ?_)
    rw [(hg y).deriv]
    rw [interior_Ici] at hy
    exact hd y (le_of_lt hy)
  have := hanti (mem_Ici.2 (le_refl (0 : ℝ))) (mem_Ici.2 hx) hx
  rwa [h0] at this

/-- The alternating Taylor bounds: for `x ≥ 0`,
`(−1)^m (cos x − cosPoly (m+1) x) ≤ 0` and `(−1)^m (sin x − sinPoly (m+1) x) ≤ 0`. -/
theorem taylor_alt (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (-1) ^ m * (cos x - cosPoly (m + 1) x) ≤ 0 ∧ (-1) ^ m * (sin x - sinPoly (m + 1) x) ≤ 0 := by
  induction m generalizing x with
  | zero =>
    have hc : ∀ y : ℝ, 0 ≤ y → (-1) ^ 0 * (cos y - cosPoly (0 + 1) y) ≤ 0 := fun y _ => by
      simpa [cosPoly] using cos_le_one y
    refine ⟨hc x hx, ?_⟩
    refine nonpos_of_deriv_nonpos (g := fun y => (-1) ^ 0 * (sin y - sinPoly (0 + 1) y))
      (g' := fun y => (-1) ^ 0 * (cos y - cosPoly (0 + 1) y))
      (fun y => ((hasDerivAt_sin y).sub (hasDerivAt_sinPoly 1 y)).const_mul _)
      (by simp [sinPoly_zero]) hc hx
  | succ m ih =>
    have hc : ∀ y : ℝ, 0 ≤ y → (-1) ^ (m + 1) * (cos y - cosPoly (m + 1 + 1) y) ≤ 0 := by
      intro y hy
      refine nonpos_of_deriv_nonpos (g := fun y => (-1) ^ (m + 1) * (cos y - cosPoly (m + 1 + 1) y))
        (g' := fun y => (-1) ^ m * (sin y - sinPoly (m + 1) y))
        (fun z => ?_) (by simp [cosPoly_succ_zero]) (fun z hz => (ih hz).2) hy
      have := ((hasDerivAt_cos z).sub (hasDerivAt_cosPoly (m + 1) z)).const_mul ((-1 : ℝ) ^ (m + 1))
      refine this.congr_deriv ?_
      rw [pow_succ]
      ring
    refine ⟨hc x hx, ?_⟩
    refine nonpos_of_deriv_nonpos (g := fun y => (-1) ^ (m + 1) * (sin y - sinPoly (m + 1 + 1) y))
      (g' := fun y => (-1) ^ (m + 1) * (cos y - cosPoly (m + 1 + 1) y))
      (fun y => ((hasDerivAt_sin y).sub (hasDerivAt_sinPoly (m + 1 + 1) y)).const_mul _)
      (by simp [sinPoly_zero]) hc hx

lemma even_neg_one_pow {m : ℕ} (h : Even m) : ((-1 : ℝ) ^ m) = 1 := h.neg_one_pow

lemma odd_neg_one_pow {m : ℕ} (h : Odd m) : ((-1 : ℝ) ^ m) = -1 := h.neg_one_pow

/-- `sin x ≤ sinPoly (2k + 1) x` for `x ≥ 0`. -/
theorem sin_le_sinPoly (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : sin x ≤ sinPoly (2 * k + 1) x := by
  have h := (taylor_alt (2 * k) hx).2
  rw [even_neg_one_pow (even_two_mul k), one_mul] at h
  linarith

/-- `sinPoly (2k + 2) x ≤ sin x` for `x ≥ 0`. -/
theorem sinPoly_le_sin (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : sinPoly (2 * k + 2) x ≤ sin x := by
  have h := (taylor_alt (2 * k + 1) hx).2
  rw [odd_neg_one_pow (odd_two_mul_add_one k)] at h
  linarith

/-- `cos x ≤ cosPoly (2k + 1) x` for `x ≥ 0`. -/
theorem cos_le_cosPoly (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : cos x ≤ cosPoly (2 * k + 1) x := by
  have h := (taylor_alt (2 * k) hx).1
  rw [even_neg_one_pow (even_two_mul k), one_mul] at h
  linarith

/-- `cosPoly (2k + 2) x ≤ cos x` for `x ≥ 0`. -/
theorem cosPoly_le_cos (k : ℕ) {x : ℝ} (hx : 0 ≤ x) : cosPoly (2 * k + 2) x ≤ cos x := by
  have h := (taylor_alt (2 * k + 1) hx).1
  rw [odd_neg_one_pow (odd_two_mul_add_one k)] at h
  linarith

/-! ## Fixed-point intervals -/

/-- The fixed-point scale `S = 2⁴⁰`: an integer `m` stands for the real number `m / S`. -/
def S : ℤ := 2 ^ 40

lemma S_pos' : (0 : ℤ) < S := by norm_num [S]

lemma S_pos : (0 : ℝ) < (S : ℝ) := by exact_mod_cast S_pos'

/-- `a / S` rounded down. -/
def fdivS (a : ℤ) : ℤ := a / S

/-- `a / S` rounded up. -/
def cdivS (a : ℤ) : ℤ := -((-a) / S)

lemma fdivS_le (a : ℤ) : ((fdivS a : ℤ) : ℝ) ≤ (a : ℝ) / S := by
  rw [le_div_iff₀ S_pos]
  have := Int.ediv_mul_le a (ne_of_gt S_pos')
  exact_mod_cast this

lemma le_cdivS (a : ℤ) : (a : ℝ) / S ≤ ((cdivS a : ℤ) : ℝ) := by
  have h := fdivS_le (-a)
  simp only [fdivS] at h
  simp only [cdivS, Int.cast_neg]
  have e : ((-a : ℤ) : ℝ) / S = -((a : ℝ) / S) := by push_cast; ring
  linarith

/-- A rational number rounded down to the grid `ℤ / S`. -/
def qdn (q : ℚ) : ℤ := ⌊q * S⌋

/-- A rational number rounded up to the grid `ℤ / S`. -/
def qup (q : ℚ) : ℤ := ⌈q * S⌉

lemma qdn_le (q : ℚ) : ((qdn q : ℤ) : ℝ) / S ≤ q := by
  rw [div_le_iff₀ S_pos]
  have h := Int.floor_le (q * S)
  have h2 : (((qdn q : ℤ) : ℚ) : ℝ) ≤ ((q * S : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h2
  exact h2

lemma le_qup (q : ℚ) : (q : ℝ) ≤ ((qup q : ℤ) : ℝ) / S := by
  rw [le_div_iff₀ S_pos]
  have h := Int.le_ceil (q * S)
  have h2 : ((q * S : ℚ) : ℝ) ≤ (((qup q : ℤ) : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h2
  exact h2

/-- An interval `[lo / S, hi / S]` with integer end points. -/
structure Iv where
  lo : ℤ
  hi : ℤ

/-- `I.Mem x`: `lo / S ≤ x ≤ hi / S`. -/
def Iv.Mem (I : Iv) (x : ℝ) : Prop := (I.lo : ℝ) / S ≤ x ∧ x ≤ (I.hi : ℝ) / S

def Iv.add (a b : Iv) : Iv := ⟨a.lo + b.lo, a.hi + b.hi⟩

def Iv.neg (a : Iv) : Iv := ⟨-a.hi, -a.lo⟩

def Iv.sub (a b : Iv) : Iv := ⟨a.lo - b.hi, a.hi - b.lo⟩

def Iv.mul (a b : Iv) : Iv :=
  ⟨fdivS (min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi))),
   cdivS (max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi)))⟩

def Iv.const (q : ℚ) : Iv := ⟨qdn q, qup q⟩

lemma Iv.mem_add {x y : ℝ} {a b : Iv} (hx : a.Mem x) (hy : b.Mem y) : (a.add b).Mem (x + y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  refine ⟨?_, ?_⟩ <;> simp only [Iv.add, Int.cast_add, add_div] <;> linarith

lemma Iv.mem_neg {x : ℝ} {a : Iv} (hx : a.Mem x) : a.neg.Mem (-x) := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩ <;> simp only [Iv.neg, Int.cast_neg, neg_div] <;> linarith

lemma Iv.mem_sub {x y : ℝ} {a b : Iv} (hx : a.Mem x) (hy : b.Mem y) : (a.sub b).Mem (x - y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  refine ⟨?_, ?_⟩ <;> simp only [Iv.sub, Int.cast_sub, sub_div] <;> linarith

lemma Iv.mem_const (q : ℚ) : (Iv.const q).Mem q := ⟨qdn_le q, le_qup q⟩

lemma min_le_mul_of_mem {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) :
    min (a * y) (b * y) ≤ x * y := by
  rcases le_total 0 y with hy | hy
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right h1 hy)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right h2 hy)

lemma mul_le_max_of_mem {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) :
    x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact (mul_le_mul_of_nonneg_right h2 hy).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_right h1 hy).trans (le_max_left _ _)

/-- A product of two reals in intervals lies between the extreme products of the corners. -/
lemma mul_mem_corners {a b c d x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) (h3 : c ≤ y) (h4 : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y
      ∧ x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have ha := min_le_mul_of_mem (y := a) h3 h4
  have hb := min_le_mul_of_mem (y := b) h3 h4
  have ha' := mul_le_max_of_mem (y := a) h3 h4
  have hb' := mul_le_max_of_mem (y := b) h3 h4
  rw [mul_comm c a, mul_comm d a, mul_comm y a] at ha ha'
  rw [mul_comm c b, mul_comm d b, mul_comm y b] at hb hb'
  constructor
  · calc min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ min (a * y) (b * y) :=
          min_le_min ha hb
      _ ≤ x * y := min_le_mul_of_mem h1 h2
  · calc x * y ≤ max (a * y) (b * y) := mul_le_max_of_mem h1 h2
      _ ≤ _ := max_le_max ha' hb'

lemma Iv.mem_mul {x y : ℝ} {a b : Iv} (hx : a.Mem x) (hy : b.Mem y) : (a.mul b).Mem (x * y) := by
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨h3, h4⟩ := hy
  have hS := S_pos
  obtain ⟨hmin, hmax⟩ := mul_mem_corners h1 h2 h3 h4
  have e : ∀ p q : ℤ, ((p : ℝ) / S) * ((q : ℝ) / S) = ((p * q : ℤ) : ℝ) / S / S := by
    intro p q; push_cast; ring
  rw [e, e, e, e] at hmin hmax
  rw [min_div_div_right hS.le, min_div_div_right hS.le, min_div_div_right hS.le,
    min_div_div_right hS.le, min_div_div_right hS.le, min_div_div_right hS.le] at hmin
  rw [max_div_div_right hS.le, max_div_div_right hS.le, max_div_div_right hS.le,
    max_div_div_right hS.le, max_div_div_right hS.le, max_div_div_right hS.le] at hmax
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ hmin
    simp only [Iv.mul]
    refine div_le_div_of_nonneg_right ((fdivS_le _).trans (le_of_eq ?_)) hS.le
    push_cast
    rfl
  · refine hmax.trans ?_
    simp only [Iv.mul]
    refine div_le_div_of_nonneg_right ((le_of_eq ?_).trans (le_cdivS _)) hS.le
    push_cast
    rfl

/-! ## Polynomial expressions -/

/-- Polynomial expressions in variables `v i` with rational constants. -/
inductive IE where
  | c : ℚ → IE
  | v : ℕ → IE
  | add : IE → IE → IE
  | sub : IE → IE → IE
  | mul : IE → IE → IE
  | neg : IE → IE

instance : Add IE := ⟨IE.add⟩
instance : Sub IE := ⟨IE.sub⟩
instance : Mul IE := ⟨IE.mul⟩
instance : Neg IE := ⟨IE.neg⟩

/-- The value of an expression. -/
def IE.eval (env : ℕ → ℝ) : IE → ℝ
  | .c q => q
  | .v i => env i
  | .add a b => a.eval env + b.eval env
  | .sub a b => a.eval env - b.eval env
  | .mul a b => a.eval env * b.eval env
  | .neg a => -a.eval env

/-- The interval value of an expression. -/
def IE.ieval (box : ℕ → Iv) : IE → Iv
  | .c q => Iv.const q
  | .v i => box i
  | .add a b => (a.ieval box).add (b.ieval box)
  | .sub a b => (a.ieval box).sub (b.ieval box)
  | .mul a b => (a.ieval box).mul (b.ieval box)
  | .neg a => (a.ieval box).neg

@[simp] lemma IE.eval_c (env : ℕ → ℝ) (q : ℚ) : (IE.c q).eval env = q := rfl
@[simp] lemma IE.eval_v (env : ℕ → ℝ) (i : ℕ) : (IE.v i).eval env = env i := rfl
@[simp] lemma IE.eval_add' (env : ℕ → ℝ) (a b : IE) : (a + b).eval env = a.eval env + b.eval env :=
  rfl
@[simp] lemma IE.eval_sub' (env : ℕ → ℝ) (a b : IE) : (a - b).eval env = a.eval env - b.eval env :=
  rfl
@[simp] lemma IE.eval_mul' (env : ℕ → ℝ) (a b : IE) : (a * b).eval env = a.eval env * b.eval env :=
  rfl
@[simp] lemma IE.eval_neg' (env : ℕ → ℝ) (a : IE) : (-a).eval env = -a.eval env := rfl

/-- **Soundness of interval evaluation.** -/
theorem IE.mem_ieval {env : ℕ → ℝ} {box : ℕ → Iv} (h : ∀ i, (box i).Mem (env i)) :
    ∀ e : IE, (e.ieval box).Mem (e.eval env)
  | .c q => Iv.mem_const q
  | .v i => h i
  | .add a b => Iv.mem_add (IE.mem_ieval h a) (IE.mem_ieval h b)
  | .sub a b => Iv.mem_sub (IE.mem_ieval h a) (IE.mem_ieval h b)
  | .mul a b => Iv.mem_mul (IE.mem_ieval h a) (IE.mem_ieval h b)
  | .neg a => Iv.mem_neg (IE.mem_ieval h a)

/-! ## `sin` and `cos` of intervals in `[0, 1]` -/

/-- The variable of the Taylor polynomials. -/
def tX : IE := .v 0

/-- `x²`. -/
def tY : IE := tX * tX

/-- `sinPoly 6` in Horner form. -/
def sin6E : IE := tX * (.c 1 - tY * (.c (1 / 6) - tY * (.c (1 / 120) - tY * (.c (1 / 5040)
  - tY * (.c (1 / 362880) - tY * .c (1 / 39916800))))))

/-- `sinPoly 7` in Horner form. -/
def sin7E : IE := tX * (.c 1 - tY * (.c (1 / 6) - tY * (.c (1 / 120) - tY * (.c (1 / 5040)
  - tY * (.c (1 / 362880) - tY * (.c (1 / 39916800) - tY * .c (1 / 6227020800)))))))

/-- `cosPoly 6` in Horner form. -/
def cos6E : IE := .c 1 - tY * (.c (1 / 2) - tY * (.c (1 / 24) - tY * (.c (1 / 720)
  - tY * (.c (1 / 40320) - tY * .c (1 / 3628800)))))

/-- `cosPoly 7` in Horner form. -/
def cos7E : IE := .c 1 - tY * (.c (1 / 2) - tY * (.c (1 / 24) - tY * (.c (1 / 720)
  - tY * (.c (1 / 40320) - tY * (.c (1 / 3628800) - tY * .c (1 / 479001600))))))

lemma sin6E_eval (x : ℝ) : sin6E.eval (fun _ => x) = sinPoly 6 x := by
  simp only [sin6E, tY, tX, IE.eval_mul', IE.eval_sub', IE.eval_v, IE.eval_c, sinPoly,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]
  ring

lemma sin7E_eval (x : ℝ) : sin7E.eval (fun _ => x) = sinPoly 7 x := by
  simp only [sin7E, tY, tX, IE.eval_mul', IE.eval_sub', IE.eval_v, IE.eval_c, sinPoly,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]
  ring

lemma cos6E_eval (x : ℝ) : cos6E.eval (fun _ => x) = cosPoly 6 x := by
  simp only [cos6E, tY, tX, IE.eval_mul', IE.eval_sub', IE.eval_v, IE.eval_c, cosPoly,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]
  ring

lemma cos7E_eval (x : ℝ) : cos7E.eval (fun _ => x) = cosPoly 7 x := by
  simp only [cos7E, tY, tX, IE.eval_mul', IE.eval_sub', IE.eval_v, IE.eval_c, cosPoly,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]
  ring

/-- The interval value of a Taylor polynomial at the grid point `m / S`. -/
lemma mem_ieval_point (e : IE) (m : ℤ) :
    (e.ieval (fun _ => ⟨m, m⟩)).Mem (e.eval (fun _ => (m : ℝ) / S)) :=
  IE.mem_ieval (fun _ => ⟨le_rfl, le_rfl⟩) e

/-- A lower bound for `sin (m / S)` (for `0 ≤ m`). -/
def sinLB (m : ℤ) : ℤ := (sin6E.ieval (fun _ => ⟨m, m⟩)).lo

/-- An upper bound for `sin (m / S)` (for `0 ≤ m`). -/
def sinUB (m : ℤ) : ℤ := (sin7E.ieval (fun _ => ⟨m, m⟩)).hi

/-- A lower bound for `cos (m / S)` (for `0 ≤ m`). -/
def cosLB (m : ℤ) : ℤ := (cos6E.ieval (fun _ => ⟨m, m⟩)).lo

/-- An upper bound for `cos (m / S)` (for `0 ≤ m`). -/
def cosUB (m : ℤ) : ℤ := (cos7E.ieval (fun _ => ⟨m, m⟩)).hi

lemma sinLB_le {m : ℤ} (hm : 0 ≤ (m : ℝ) / S) : (sinLB m : ℝ) / S ≤ Real.sin ((m : ℝ) / S) := by
  have h := (mem_ieval_point sin6E m).1
  rw [sin6E_eval] at h
  exact h.trans (sinPoly_le_sin 2 hm)

lemma le_sinUB {m : ℤ} (hm : 0 ≤ (m : ℝ) / S) : Real.sin ((m : ℝ) / S) ≤ (sinUB m : ℝ) / S := by
  have h := (mem_ieval_point sin7E m).2
  rw [sin7E_eval] at h
  exact (sin_le_sinPoly 3 hm).trans h

lemma cosLB_le {m : ℤ} (hm : 0 ≤ (m : ℝ) / S) : (cosLB m : ℝ) / S ≤ Real.cos ((m : ℝ) / S) := by
  have h := (mem_ieval_point cos6E m).1
  rw [cos6E_eval] at h
  exact h.trans (cosPoly_le_cos 2 hm)

lemma le_cosUB {m : ℤ} (hm : 0 ≤ (m : ℝ) / S) : Real.cos ((m : ℝ) / S) ≤ (cosUB m : ℝ) / S := by
  have h := (mem_ieval_point cos7E m).2
  rw [cos7E_eval] at h
  exact (cos_le_cosPoly 3 hm).trans h

def Iv.sin (a : Iv) : Iv := if 0 ≤ a.lo ∧ a.hi ≤ S then ⟨sinLB a.lo, sinUB a.hi⟩ else ⟨-S, S⟩

def Iv.cos (a : Iv) : Iv := if 0 ≤ a.lo ∧ a.hi ≤ S then ⟨cosLB a.hi, cosUB a.lo⟩ else ⟨-S, S⟩

lemma Iv.mem_sin {x : ℝ} {a : Iv} (hx : a.Mem x) : a.sin.Mem (Real.sin x) := by
  have hS := S_pos
  have hpi := pi_gt_three
  unfold Iv.sin
  split_ifs with h
  · obtain ⟨h0, h1⟩ := h
    have hlo : (0 : ℝ) ≤ (a.lo : ℝ) / S := div_nonneg (by exact_mod_cast h0) hS.le
    have hhi : (a.hi : ℝ) / S ≤ 1 := by rw [div_le_one hS]; exact_mod_cast h1
    refine ⟨?_, ?_⟩
    · exact (sinLB_le hlo).trans (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith)
        (by linarith [hx.2]) hx.1)
    · exact (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hx.1]) (by linarith)
        hx.2).trans (le_sinUB (hlo.trans (hx.1.trans hx.2)))
  · refine ⟨?_, ?_⟩
    · rw [Int.cast_neg, neg_div, div_self hS.ne']; exact Real.neg_one_le_sin x
    · rw [div_self hS.ne']; exact Real.sin_le_one x

lemma Iv.mem_cos {x : ℝ} {a : Iv} (hx : a.Mem x) : a.cos.Mem (Real.cos x) := by
  have hS := S_pos
  have hpi := pi_gt_three
  unfold Iv.cos
  split_ifs with h
  · obtain ⟨h0, h1⟩ := h
    have hlo : (0 : ℝ) ≤ (a.lo : ℝ) / S := div_nonneg (by exact_mod_cast h0) hS.le
    have hhi : (a.hi : ℝ) / S ≤ 1 := by rw [div_le_one hS]; exact_mod_cast h1
    refine ⟨?_, ?_⟩
    · exact (cosLB_le (hlo.trans (hx.1.trans hx.2))).trans
        (Real.cos_le_cos_of_nonneg_of_le_pi (hlo.trans hx.1) (by linarith) hx.2)
    · exact (Real.cos_le_cos_of_nonneg_of_le_pi hlo (by linarith [hx.2]) hx.1).trans
        (le_cosUB hlo)
  · refine ⟨?_, ?_⟩
    · rw [Int.cast_neg, neg_div, div_self hS.ne']; exact Real.neg_one_le_cos x
    · rw [div_self hS.ne']; exact Real.cos_le_one x

/-- An expression whose interval value is strictly negative or strictly positive does not vanish. -/
def Iv.nonzero (I : Iv) : Bool := decide (I.hi < 0) || decide (0 < I.lo)

lemma Iv.ne_zero_of_nonzero {x : ℝ} {I : Iv} (hx : I.Mem x) (h : I.nonzero = true) : x ≠ 0 := by
  have hS := S_pos
  unfold Iv.nonzero at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · have h' : I.hi < 0 := of_decide_eq_true h
    have : (I.hi : ℝ) / S < 0 := div_neg_of_neg_of_pos (by exact_mod_cast h') hS
    exact ne_of_lt (hx.2.trans_lt this)
  · have h' : 0 < I.lo := of_decide_eq_true h
    have : 0 < (I.lo : ℝ) / S := div_pos (by exact_mod_cast h') hS
    exact ne_of_gt (this.trans_le hx.1)

/-- A bound for the absolute value on an interval: `max (−lo) hi`. -/
def Iv.mag (I : Iv) : ℤ := max (-I.lo) I.hi

lemma Iv.abs_le_mag {x : ℝ} {I : Iv} (hx : I.Mem x) : |x| ≤ (I.mag : ℝ) / S := by
  have hS := S_pos
  have h1 : ((-I.lo : ℤ) : ℝ) / S ≤ (I.mag : ℝ) / S :=
    div_le_div_of_nonneg_right (by exact_mod_cast le_max_left _ _) hS.le
  have h2 : (I.hi : ℝ) / S ≤ (I.mag : ℝ) / S :=
    div_le_div_of_nonneg_right (by exact_mod_cast le_max_right _ _) hS.le
  rw [Int.cast_neg, neg_div] at h1
  rw [abs_le]
  exact ⟨by linarith [hx.1], hx.2.trans h2⟩

/-- The point interval `[1, 1]`. -/
lemma Iv.mem_one : (⟨S, S⟩ : Iv).Mem 1 := by
  have hS := S_pos
  exact ⟨(div_self hS.ne').le, (div_self hS.ne').ge⟩

/-- A point on a segment between two points of an interval lies in the interval. -/
lemma Iv.mem_line {I : Iv} {a b τ : ℝ} (ha : I.Mem a) (hb : I.Mem b) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    I.Mem (a + τ * (b - a)) := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  have e : a + τ * (b - a) = (1 - τ) * a + τ * b := by ring
  rw [e]
  constructor <;> nlinarith

/-! ## Derivatives of expressions -/

/-- The derivative of the value of an expression, in forward mode: `δ i` is the derivative of the
variable `i`. -/
def IE.evalD (env δ : ℕ → ℝ) : IE → ℝ
  | .c _ => 0
  | .v i => δ i
  | .add a b => a.evalD env δ + b.evalD env δ
  | .sub a b => a.evalD env δ - b.evalD env δ
  | .mul a b => a.evalD env δ * b.eval env + a.eval env * b.evalD env δ
  | .neg a => -a.evalD env δ

/-- **Chain rule**: along a path of environments `ρ`, the value of an expression has derivative
`evalD`. -/
theorem IE.hasDerivAt_eval {ρ : ℝ → ℕ → ℝ} {δ : ℕ → ℝ} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s => ρ s i) (δ i) t) :
    ∀ e : IE, HasDerivAt (fun s => e.eval (ρ s)) (e.evalD (ρ t) δ) t
  | .c q => hasDerivAt_const t (q : ℝ)
  | .v i => h i
  | .add a b => (IE.hasDerivAt_eval h a).add (IE.hasDerivAt_eval h b)
  | .sub a b => (IE.hasDerivAt_eval h a).sub (IE.hasDerivAt_eval h b)
  | .mul a b => (IE.hasDerivAt_eval h a).mul (IE.hasDerivAt_eval h b)
  | .neg a => (IE.hasDerivAt_eval h a).neg

/-- `evalD` is linear in the derivatives of the variables. -/
theorem IE.evalD_lin (env δ₁ δ₂ : ℕ → ℝ) (u w : ℝ) :
    ∀ e : IE, e.evalD env (fun i => u * δ₁ i + w * δ₂ i) = u * e.evalD env δ₁ + w * e.evalD env δ₂
  | .c _ => by simp only [IE.evalD]; ring
  | .v _ => rfl
  | .add a b => by
    simp only [IE.evalD, IE.evalD_lin env δ₁ δ₂ u w a, IE.evalD_lin env δ₁ δ₂ u w b]; ring
  | .sub a b => by
    simp only [IE.evalD, IE.evalD_lin env δ₁ δ₂ u w a, IE.evalD_lin env δ₁ δ₂ u w b]; ring
  | .mul a b => by
    simp only [IE.evalD, IE.evalD_lin env δ₁ δ₂ u w a, IE.evalD_lin env δ₁ δ₂ u w b]; ring
  | .neg a => by simp only [IE.evalD, IE.evalD_lin env δ₁ δ₂ u w a]; ring

/-- The derivative of an expression, as an expression: `d i` is the derivative of the variable
`i`. -/
def IE.diff (d : ℕ → IE) : IE → IE
  | .c _ => .c 0
  | .v i => d i
  | .add a b => .add (a.diff d) (b.diff d)
  | .sub a b => .sub (a.diff d) (b.diff d)
  | .mul a b => .add (.mul (a.diff d) b) (.mul a (b.diff d))
  | .neg a => .neg (a.diff d)

theorem IE.eval_diff (env : ℕ → ℝ) (d : ℕ → IE) :
    ∀ e : IE, (e.diff d).eval env = e.evalD env (fun i => (d i).eval env)
  | .c _ => by simp [IE.diff, IE.evalD]
  | .v _ => rfl
  | .add a b => by
    simp only [IE.diff, IE.evalD, IE.eval, IE.eval_diff env d a, IE.eval_diff env d b]
  | .sub a b => by
    simp only [IE.diff, IE.evalD, IE.eval, IE.eval_diff env d a, IE.eval_diff env d b]
  | .mul a b => by
    simp only [IE.diff, IE.evalD, IE.eval, IE.eval_diff env d a, IE.eval_diff env d b]
  | .neg a => by simp only [IE.diff, IE.evalD, IE.eval, IE.eval_diff env d a]

end Sofa.IA
