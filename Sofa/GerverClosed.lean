/-
# Sofa/GerverClosed.lean — closed forms of Gerver's integrals `x`, `y` and of the path `p`

On each of the four pieces `[0, φ]`, `[φ, θ]`, `[θ, π/2 − θ]`, `[π/2 − θ, π/2 − φ]` the radius
function `r` is a polynomial `ra k + rb k · t + rc k · t²` of degree at most two (`r_eq_quad`), so
the integrals `x`, `y` have closed forms there (`y_eq_yC`, `x_eq_xC`), built from the antiderivatives
`Fs`, `Fc` of `(a + b t + c t²) sin t`, `(a + b t + c t²) cos t`.  Consequently each coordinate of
Gerver's path `p` is, on each of the five pieces `[0, φ]`, …, `[π/2 − φ, π/2]` of `[0, π/2]`, an
explicit expression in `α`, `sin α`, `cos α` and the constants (`p₁_eq_closed`, `p₂_eq_closed`).

The closed forms are also written as interval expressions `IE` (in the variables
`α, sin α, cos α, φ, θ, π, sin φ, cos φ, sin θ, cos θ, A, B`), with `eval` lemmas, so that
inequalities about `p` can be certified by interval arithmetic (`Sofa/GerverConn.lean`).

STATUS: [PROOF-C-local] round 38 (2026-09-23, Opus 5.5).
-/
import Sofa.GerverPath

noncomputable section

open Real Set MeasureTheory intervalIntegral MovingSofa

namespace Sofa.GP

open GC IA
open MovingSofa.GerversSofa (A B φ θ r)

/-! ## Antiderivatives -/

/-- `−(a + b t + c t²) C + (b + 2 c t) S + 2 c C`: with `S = sin t`, `C = cos t` an antiderivative
of `(a + b t + c t²) sin t`. -/
def Fs (a b c t s co : ℝ) : ℝ := -(a + b * t + c * t ^ 2) * co + (b + 2 * c * t) * s + 2 * c * co

/-- `(a + b t + c t²) S + (b + 2 c t) C − 2 c S`: with `S = sin t`, `C = cos t` an antiderivative
of `(a + b t + c t²) cos t`. -/
def Fc (a b c t s co : ℝ) : ℝ := (a + b * t + c * t ^ 2) * s + (b + 2 * c * t) * co - 2 * c * s

lemma integral_quad_sin (a b c l m : ℝ) :
    ∫ t in l..m, (a + b * t + c * t ^ 2) * sin t
      = Fs a b c m (sin m) (cos m) - Fs a b c l (sin l) (cos l) := by
  rw [integral_quad_mul_sin]; simp only [Fs]

lemma integral_quad_cos (a b c l m : ℝ) :
    ∫ t in l..m, (a + b * t + c * t ^ 2) * cos t
      = Fc a b c m (sin m) (cos m) - Fc a b c l (sin l) (cos l) := by
  refine integral_eq_sub_of_hasDerivAt
    (f := fun t => Fc a b c t (sin t) (cos t)) (fun t _ => ?_) ((by fun_prop : Continuous
      fun t => (a + b * t + c * t ^ 2) * cos t).intervalIntegrable _ _)
  have hg : HasDerivAt (fun t => a + b * t + c * t ^ 2) (b + 2 * c * t) t :=
    ((((hasDerivAt_id' t).const_mul b).const_add a).fun_add
      ((hasDerivAt_pow 2 t).const_mul c)).congr_deriv (by norm_num; ring)
  have hg' : HasDerivAt (fun t => b + 2 * c * t) (2 * c) t :=
    (((hasDerivAt_id' t).const_mul (2 * c)).const_add b).congr_deriv (by ring)
  exact (((hg.fun_mul (hasDerivAt_sin t)).fun_add (hg'.fun_mul (hasDerivAt_cos t))).fun_sub
    ((hasDerivAt_sin t).const_mul (2 * c))).congr_deriv (by ring)

/-! ## The pieces -/

/-- The break points `0, φ, θ, π/2 − θ, π/2 − φ, π/2`. -/
def brk : ℕ → ℝ
  | 0 => 0
  | 1 => φ
  | 2 => θ
  | 3 => π / 2 - θ
  | 4 => π / 2 - φ
  | _ => π / 2

/-- Coefficients of `r` on the pieces. -/
def ra : ℕ → ℝ
  | 0 => 1 / 2
  | 1 => (1 + A - φ) / 2
  | 2 => A - φ
  | _ => B - (π / 2 - φ) * (1 + A) / 2 - (π / 2 - φ) ^ 2 / 4

def rb : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / 2
  | 2 => 1
  | _ => (1 + A) / 2 + (π / 2 - φ) / 2

def rc : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | _ => -1 / 4

lemma brk_mono : brk 0 < brk 1 ∧ brk 1 < brk 2 ∧ brk 2 < brk 3 ∧ brk 3 < brk 4 ∧
    brk 4 < brk 5 := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  simp only [brk]
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- On the piece `(brk k, brk (k + 1)]`, `r` is the polynomial `ra k + rb k t + rc k t²`. -/
lemma r_eq_quad {k : ℕ} (hk : k ≤ 3) {t : ℝ} (ht : t ∈ Ioc (brk k) (brk (k + 1))) :
    r t = ra k + rb k * t + rc k * t ^ 2 := by
  interval_cases k
  · rw [r_of_le_φ ht.2]; simp [ra, rb, rc]
  · rw [r_piece₂ ht]; simp only [ra, rb, rc]; ring
  · rw [r_piece₃ ht]; simp only [ra, rb, rc]; ring
  · rw [r_piece₄ ht]; simp only [ra, rb, rc]; ring

lemma integral_piece_sin {k : ℕ} (hk : k ≤ 3) {l m : ℝ} (hl : brk k ≤ l) (hlm : l ≤ m)
    (hm : m ≤ brk (k + 1)) :
    ∫ t in l..m, r t * sin t = Fs (ra k) (rb k) (rc k) m (sin m) (cos m)
      - Fs (ra k) (rb k) (rc k) l (sin l) (cos l) := by
  rw [← integral_quad_sin]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le hlm] at ht
  rw [r_eq_quad hk ⟨hl.trans_lt ht.1, ht.2.trans hm⟩]

lemma integral_piece_cos {k : ℕ} (hk : k ≤ 3) {l m : ℝ} (hl : brk k ≤ l) (hlm : l ≤ m)
    (hm : m ≤ brk (k + 1)) :
    ∫ t in l..m, r t * cos t = Fc (ra k) (rb k) (rc k) m (sin m) (cos m)
      - Fc (ra k) (rb k) (rc k) l (sin l) (cos l) := by
  rw [← integral_quad_cos]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le hlm] at ht
  rw [r_eq_quad hk ⟨hl.trans_lt ht.1, ht.2.trans hm⟩]

/-- `∫` of `r sin` over the whole piece `k`. -/
def SY (k : ℕ) : ℝ := Fs (ra k) (rb k) (rc k) (brk (k + 1)) (sin (brk (k + 1))) (cos (brk (k + 1)))
  - Fs (ra k) (rb k) (rc k) (brk k) (sin (brk k)) (cos (brk k))

/-- `∫` of `r cos` over the whole piece `k`. -/
def SX (k : ℕ) : ℝ := Fc (ra k) (rb k) (rc k) (brk (k + 1)) (sin (brk (k + 1))) (cos (brk (k + 1)))
  - Fc (ra k) (rb k) (rc k) (brk k) (sin (brk k)) (cos (brk k))

/-- The tail sums `∑_{j = k}^{3} SY j`. -/
def tailY : ℕ → ℝ
  | 0 => SY 0 + SY 1 + SY 2 + SY 3
  | 1 => SY 1 + SY 2 + SY 3
  | 2 => SY 2 + SY 3
  | 3 => SY 3
  | _ => 0

def tailX : ℕ → ℝ
  | 0 => SX 0 + SX 1 + SX 2 + SX 3
  | 1 => SX 1 + SX 2 + SX 3
  | 2 => SX 2 + SX 3
  | 3 => SX 3
  | _ => 0

lemma intervalIntegrable_r_sin (a b : ℝ) : IntervalIntegrable (fun t => r t * sin t) volume a b :=
  intervalIntegrable_r_mul continuous_sin a b

lemma intervalIntegrable_r_cos (a b : ℝ) : IntervalIntegrable (fun t => r t * cos t) volume a b :=
  intervalIntegrable_r_mul continuous_cos a b

/-- `∫_{brk k}^{π/2 − φ} r sin = tailY k`. -/
lemma integral_tail_sin {k : ℕ} (hk : k ≤ 4) :
    ∫ t in brk k..(π / 2 - φ), r t * sin t = tailY k := by
  obtain ⟨h01, h12, h23, h34, -⟩ := brk_mono
  have e : π / 2 - φ = brk 4 := rfl
  have hp : ∀ j, j ≤ 3 → ∫ t in brk j..brk (j + 1), r t * sin t = SY j := fun j hj =>
    integral_piece_sin hj le_rfl (by interval_cases j <;> linarith) le_rfl
  have hi := intervalIntegrable_r_sin
  rw [e]
  interval_cases k
  · rw [← integral_add_adjacent_intervals (hi _ (brk 3)) (hi _ _),
      ← integral_add_adjacent_intervals (hi _ (brk 2)) (hi _ _),
      ← integral_add_adjacent_intervals (hi _ (brk 1)) (hi _ _), hp 0 (by norm_num),
      hp 1 (by norm_num), hp 2 (by norm_num), hp 3 (by norm_num)]
    rfl
  · rw [← integral_add_adjacent_intervals (hi _ (brk 3)) (hi _ _),
      ← integral_add_adjacent_intervals (hi _ (brk 2)) (hi _ _), hp 1 (by norm_num),
      hp 2 (by norm_num), hp 3 (by norm_num)]
    rfl
  · rw [← integral_add_adjacent_intervals (hi _ (brk 3)) (hi _ _), hp 2 (by norm_num),
      hp 3 (by norm_num)]
    rfl
  · rw [hp 3 (by norm_num)]; rfl
  · rw [integral_same]; rfl

lemma integral_tail_cos {k : ℕ} (hk : k ≤ 4) :
    ∫ t in brk k..(π / 2 - φ), r t * cos t = tailX k := by
  obtain ⟨h01, h12, h23, h34, -⟩ := brk_mono
  have e : π / 2 - φ = brk 4 := rfl
  have hp : ∀ j, j ≤ 3 → ∫ t in brk j..brk (j + 1), r t * cos t = SX j := fun j hj =>
    integral_piece_cos hj le_rfl (by interval_cases j <;> linarith) le_rfl
  have hi := intervalIntegrable_r_cos
  rw [e]
  interval_cases k
  · rw [← integral_add_adjacent_intervals (hi _ (brk 3)) (hi _ _),
      ← integral_add_adjacent_intervals (hi _ (brk 2)) (hi _ _),
      ← integral_add_adjacent_intervals (hi _ (brk 1)) (hi _ _), hp 0 (by norm_num),
      hp 1 (by norm_num), hp 2 (by norm_num), hp 3 (by norm_num)]
    rfl
  · rw [← integral_add_adjacent_intervals (hi _ (brk 3)) (hi _ _),
      ← integral_add_adjacent_intervals (hi _ (brk 2)) (hi _ _), hp 1 (by norm_num),
      hp 2 (by norm_num), hp 3 (by norm_num)]
    rfl
  · rw [← integral_add_adjacent_intervals (hi _ (brk 3)) (hi _ _), hp 2 (by norm_num),
      hp 3 (by norm_num)]
    rfl
  · rw [hp 3 (by norm_num)]; rfl
  · rw [integral_same]; rfl

/-- The closed form of `y` on the piece `k`, with `S`, `C` standing for `sin β`, `cos β`. -/
def yC (k : ℕ) (β s co : ℝ) : ℝ :=
  Fs (ra k) (rb k) (rc k) (brk (k + 1)) (sin (brk (k + 1))) (cos (brk (k + 1)))
    - Fs (ra k) (rb k) (rc k) β s co + tailY (k + 1)

/-- The closed form of `x` on the piece `k`. -/
def xC (k : ℕ) (β s co : ℝ) : ℝ :=
  1 - (Fc (ra k) (rb k) (rc k) (brk (k + 1)) (sin (brk (k + 1))) (cos (brk (k + 1)))
    - Fc (ra k) (rb k) (rc k) β s co + tailX (k + 1))

/-- **`y` in closed form** on the piece `[brk k, brk (k + 1)]`. -/
theorem y_eq_yC {k : ℕ} (hk : k ≤ 3) {β : ℝ} (hβ : β ∈ Icc (brk k) (brk (k + 1))) :
    GerversSofa.y β = yC k β (sin β) (cos β) := by
  rw [GerversSofa.y, ← integral_add_adjacent_intervals (intervalIntegrable_r_sin _ (brk (k + 1)))
    (intervalIntegrable_r_sin _ _), integral_piece_sin hk hβ.1 hβ.2 le_rfl,
    integral_tail_sin (by omega), yC]

/-- **`x` in closed form** on the piece `[brk k, brk (k + 1)]`. -/
theorem x_eq_xC {k : ℕ} (hk : k ≤ 3) {β : ℝ} (hβ : β ∈ Icc (brk k) (brk (k + 1))) :
    GerversSofa.x β = xC k β (sin β) (cos β) := by
  rw [GerversSofa.x, ← integral_add_adjacent_intervals (intervalIntegrable_r_cos _ (brk (k + 1)))
    (intervalIntegrable_r_cos _ _), integral_piece_cos hk hβ.1 hβ.2 le_rfl,
    integral_tail_cos (by omega), xC]

/-- `x 0` in closed form. -/
def x0C : ℝ := xC 0 0 0 1

lemma x_zero_eq : GerversSofa.x 0 = x0C := by
  obtain ⟨h01, -⟩ := brk_mono
  have := x_eq_xC (k := 0) (by norm_num) (β := 0) ⟨le_rfl, h01.le⟩
  rw [this, sin_zero, cos_zero]; rfl

/-! ## The path `p` in closed form -/

/-- The first coordinate of `p` on the five pieces of `[0, π/2]`. -/
def p₁C (j : ℕ) (α : ℝ) : ℝ :=
  match j with
  | 0 => cos α - 1
  | 1 => xC 3 (π / 2 - α) (cos α) (sin α) * cos α + yC 3 (π / 2 - α) (cos α) (sin α) * sin α - 1
  | 2 => xC 2 (π / 2 - α) (cos α) (sin α) * cos α + yC 2 (π / 2 - α) (cos α) (sin α) * sin α - 1
  | 3 => xC 1 (π / 2 - α) (cos α) (sin α) * cos α + yC 1 (π / 2 - α) (cos α) (sin α) * sin α - 1
  | _ => xC 0 (π / 2 - α) (cos α) (sin α) * cos α + yC 0 (π / 2 - α) (cos α) (sin α) * sin α - 1

/-- The second coordinate of `p` on the five pieces of `[0, π/2]`. -/
def p₂C (j : ℕ) (α : ℝ) : ℝ :=
  match j with
  | 0 => yC 0 α (sin α) (cos α) * cos α - (4 * x0C - 2 - xC 0 α (sin α) (cos α)) * sin α - 1
  | 1 => yC 1 α (sin α) (cos α) * cos α - (4 * x0C - 2 - xC 1 α (sin α) (cos α)) * sin α - 1
  | 2 => yC 2 α (sin α) (cos α) * cos α - (4 * x0C - 2 - xC 2 α (sin α) (cos α)) * sin α - 1
  | 3 => yC 3 α (sin α) (cos α) * cos α - (4 * x0C - 2 - xC 3 α (sin α) (cos α)) * sin α - 1
  | _ => -(4 * x0C - 3) * sin α - 1

/-- The five pieces of `[0, π/2]`: the reflection `α ↦ π/2 − α` maps piece `j` of `α` to piece
`4 − j` of `β` (`j ≥ 1`). -/
lemma brk_reflect (j : ℕ) (hj : 1 ≤ j) (hj' : j ≤ 4) :
    π / 2 - brk (j + 1) = brk (4 - j) ∧ π / 2 - brk j = brk (4 - j + 1) := by
  interval_cases j
  · exact ⟨rfl, rfl⟩
  · exact ⟨show π / 2 - (π / 2 - θ) = θ by ring, rfl⟩
  · exact ⟨show π / 2 - (π / 2 - φ) = φ by ring, show π / 2 - (π / 2 - θ) = θ by ring⟩
  · exact ⟨show π / 2 - π / 2 = (0 : ℝ) by ring, show π / 2 - (π / 2 - φ) = φ by ring⟩

/-- **`p₁` in closed form** on the piece `j` of `[0, π/2]`. -/
theorem p₁_eq_closed {j : ℕ} (hj : j ≤ 4) {α : ℝ} (hα : α ∈ Icc (brk j) (brk (j + 1))) :
    p₁ α = p₁C j α := by
  obtain ⟨h01, h12, h23, h34, h45⟩ := brk_mono
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [p₁, if_pos (show α ≤ φ from hα.2)]; rfl
  obtain ⟨e1, e2⟩ := brk_reflect j hj0 hj
  have hβ : π / 2 - α ∈ Icc (brk (4 - j)) (brk (4 - j + 1)) :=
    ⟨by rw [← e1]; linarith [hα.2], by rw [← e2]; linarith [hα.1]⟩
  have hx := x_eq_xC (k := 4 - j) (by omega) hβ
  have hy := y_eq_yC (k := 4 - j) (by omega) hβ
  rw [sin_pi_div_two_sub, cos_pi_div_two_sub] at hx hy
  have hbranch : p₁ α = GerversSofa.x (π / 2 - α) * cos α + GerversSofa.y (π / 2 - α) * sin α - 1 := by
    rw [p₁]
    split_ifs with h
    · have hαφ : α = φ := le_antisymm h (by
        have : brk 1 ≤ brk j := by
          interval_cases j <;> first | exact le_rfl | linarith
        exact this.trans hα.1)
      subst hαφ
      rw [x_end, y_end]; ring
    · rfl
  rw [hbranch, hx, hy]
  interval_cases j <;> rfl

/-- **`p₂` in closed form** on the piece `j` of `[0, π/2]`. -/
theorem p₂_eq_closed {j : ℕ} (hj : j ≤ 4) {α : ℝ} (hα : α ∈ Icc (brk j) (brk (j + 1))) :
    p₂ α = p₂C j α := by
  obtain ⟨h01, h12, h23, h34, h45⟩ := brk_mono
  rcases Nat.lt_or_ge j 4 with hj4 | hj4
  · have hα4 : α ≤ π / 2 - φ := by
      have : brk (j + 1) ≤ brk 4 := by
        interval_cases j <;> first | exact le_rfl | linarith
      exact hα.2.trans this
    rw [p₂, if_pos hα4, y_eq_yC (by omega) hα, x_eq_xC (by omega) hα, x_zero_eq]
    interval_cases j <;> rfl
  · have hj' : j = 4 := le_antisymm hj hj4
    subst hj'
    rw [p₂]
    split_ifs with h
    · have hαe : α = π / 2 - φ := le_antisymm h hα.1
      subst hαe
      rw [x_end, y_end, x_zero_eq]; simp only [p₂C]; ring
    · rw [x_zero_eq]; rfl

end Sofa.GP
