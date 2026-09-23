/-
# Sofa/GerverUnique.lean — existence and uniqueness of Gerver's constants

Romik's system `Spec A B φ θ` (a verbatim copy of the upstream `ABφθSpec`) has **exactly one
solution** (`spec_existsUnique`); this proves the upstream `ABφθSpec.existsUnique`.  Moreover every
solution has `|φ − φ₀|, |θ − θ₀| ≤ 2⁻³⁰` (`Spec_mem_tbox`), which gives Gerver's angle bounds
`0 < φ ≤ 1/25`, `φ < θ < π/4` (`Spec_angles`).

The method is a **verified simplified Newton (Krawczyk-type) argument**:

* `Spec_mem_target` (`GerverConst.lean`) puts every solution in the box `target` of half-width
  `2⁻⁹`, where the reduced equations `F = (Q̃, R̃)` vanish.
* With a fixed matrix `P ≈ F'(x*)⁻¹`, the map `T(x) = x − P F(x)` (`Tmap`) is a contraction with
  constant `1/2` in the max-norm on `target` (`lip_of_contrOK`): the partial derivatives of
  `P F` are enclosed by interval arithmetic (`IE.diff`, `contrOK_target`), and the mean value
  theorem along segments (`IE_mvt`) turns this into the Lipschitz bound.
* `T` maps the tight box `tbox` (half-width `2⁻³⁰`) into itself (`maps_tbox`, from an interval
  evaluation of `P F` at the center, `mapOK_true`), so Banach's fixed-point theorem gives a fixed
  point, i.e. a zero of `F` (`exists_fixed`).  From it `A = N₁ / (3 cos φ − cos θ)` and
  `B = A κ + c₀` solve the whole system (`spec_of_zero`).
* Two zeros of `F` in `target` are fixed points of the contraction, hence equal
  (`fixed_unique`); `A`, `B` are then determined by `E₁ − 2E₃` and `E₄`.

Everything is proved; the computations are checked by the kernel (`decide +kernel`).

STATUS: [PROOF-C-local] round 37 (2026-09-23, Opus 5.5).
-/
import Sofa.GerverConst

noncomputable section

open Real Set Filter Topology

namespace Sofa.GC

open IA

/-! ## Partial derivatives and the mean value theorem -/

/-- Derivatives of the variables in the direction of `φ`. -/
def dφ : ℕ → IE
  | 0 => k 1
  | 3 => cφ
  | 4 => -sφ
  | _ => k 0

/-- Derivatives of the variables in the direction of `θ`. -/
def dθ : ℕ → IE
  | 1 => k 1
  | 5 => cθ
  | 6 => -sθ
  | _ => k 0

/-- The environment at the point `y + τ (x − y)` of the segment from `y` to `x`. -/
def lineEnv (y x : ℝ × ℝ) (τ : ℝ) : ℕ → ℝ :=
  envOf (y.1 + τ * (x.1 - y.1)) (y.2 + τ * (x.2 - y.2))

/-- Along the segment from `y` to `x`, the variables have derivatives
`(x₁ − y₁) · dφ + (x₂ − y₂) · dθ`. -/
lemma hasDerivAt_lineEnv (y x : ℝ × ℝ) (s : ℝ) (i : ℕ) :
    HasDerivAt (fun τ => lineEnv y x τ i)
      ((x.1 - y.1) * (dφ i).eval (lineEnv y x s) + (x.2 - y.2) * (dθ i).eval (lineEnv y x s)) s := by
  have hφ : HasDerivAt (fun τ => y.1 + τ * (x.1 - y.1)) (x.1 - y.1) s := by
    simpa using ((hasDerivAt_id s).mul_const (x.1 - y.1)).const_add y.1
  have hθ : HasDerivAt (fun τ => y.2 + τ * (x.2 - y.2)) (x.2 - y.2) s := by
    simpa using ((hasDerivAt_id s).mul_const (x.2 - y.2)).const_add y.2
  match i with
  | 0 =>
    refine hφ.congr_deriv ?_
    change x.1 - y.1 = (x.1 - y.1) * ((1 : ℚ) : ℝ) + (x.2 - y.2) * ((0 : ℚ) : ℝ)
    simp
  | 1 =>
    refine hθ.congr_deriv ?_
    change x.2 - y.2 = (x.1 - y.1) * ((0 : ℚ) : ℝ) + (x.2 - y.2) * ((1 : ℚ) : ℝ)
    simp
  | 2 =>
    refine (hasDerivAt_const s π).congr_deriv ?_
    change (0 : ℝ) = (x.1 - y.1) * ((0 : ℚ) : ℝ) + (x.2 - y.2) * ((0 : ℚ) : ℝ)
    simp
  | 3 =>
    refine hφ.sin.congr_deriv ?_
    change Real.cos (y.1 + s * (x.1 - y.1)) * (x.1 - y.1)
      = (x.1 - y.1) * Real.cos (y.1 + s * (x.1 - y.1)) + (x.2 - y.2) * ((0 : ℚ) : ℝ)
    simp only [Rat.cast_zero, mul_zero, add_zero]
    ring
  | 4 =>
    refine hφ.cos.congr_deriv ?_
    change -Real.sin (y.1 + s * (x.1 - y.1)) * (x.1 - y.1)
      = (x.1 - y.1) * -Real.sin (y.1 + s * (x.1 - y.1)) + (x.2 - y.2) * ((0 : ℚ) : ℝ)
    simp only [Rat.cast_zero, mul_zero, add_zero]
    ring
  | 5 =>
    refine hθ.sin.congr_deriv ?_
    change Real.cos (y.2 + s * (x.2 - y.2)) * (x.2 - y.2)
      = (x.1 - y.1) * ((0 : ℚ) : ℝ) + (x.2 - y.2) * Real.cos (y.2 + s * (x.2 - y.2))
    simp only [Rat.cast_zero, mul_zero, zero_add]
    ring
  | 6 =>
    refine hθ.cos.congr_deriv ?_
    change -Real.sin (y.2 + s * (x.2 - y.2)) * (x.2 - y.2)
      = (x.1 - y.1) * ((0 : ℚ) : ℝ) + (x.2 - y.2) * -Real.sin (y.2 + s * (x.2 - y.2))
    simp only [Rat.cast_zero, mul_zero, zero_add]
    ring
  | _ + 7 =>
    refine (hasDerivAt_const s (0 : ℝ)).congr_deriv ?_
    change (0 : ℝ) = (x.1 - y.1) * ((0 : ℚ) : ℝ) + (x.2 - y.2) * ((0 : ℚ) : ℝ)
    simp

lemma lineEnv_one (y x : ℝ × ℝ) : lineEnv y x 1 = envOf x.1 x.2 := by
  unfold lineEnv
  congr 1 <;> ring

lemma lineEnv_zero (y x : ℝ × ℝ) : lineEnv y x 0 = envOf y.1 y.2 := by
  unfold lineEnv
  congr 1 <;> ring

/-- **Mean value theorem** for an expression in `(φ, θ)`, with the partial derivatives
`e.diff dφ`, `e.diff dθ` at a point of the segment. -/
theorem IE_mvt (e : IE) (x y : ℝ × ℝ) : ∃ τ ∈ Ioo (0 : ℝ) 1,
    e.eval (envOf x.1 x.2) - e.eval (envOf y.1 y.2) =
      (x.1 - y.1) * (e.diff dφ).eval (lineEnv y x τ) + (x.2 - y.2) * (e.diff dθ).eval (lineEnv y x τ) := by
  have hg : ∀ s, HasDerivAt (fun τ => e.eval (lineEnv y x τ))
      ((x.1 - y.1) * (e.diff dφ).eval (lineEnv y x s)
        + (x.2 - y.2) * (e.diff dθ).eval (lineEnv y x s)) s := by
    intro s
    have h := IE.hasDerivAt_eval (ρ := lineEnv y x) (t := s) (hasDerivAt_lineEnv y x s) e
    rw [IE.evalD_lin, ← IE.eval_diff, ← IE.eval_diff] at h
    exact h
  obtain ⟨τ, hτ, hτ'⟩ := exists_hasDerivAt_eq_slope (fun τ => e.eval (lineEnv y x τ))
    (fun s => (x.1 - y.1) * (e.diff dφ).eval (lineEnv y x s)
      + (x.2 - y.2) * (e.diff dθ).eval (lineEnv y x s)) zero_lt_one
    (fun s _ => (hg s).continuousAt.continuousWithinAt) (fun s _ => hg s)
  refine ⟨τ, hτ, ?_⟩
  simp only [lineEnv_one, lineEnv_zero, sub_zero, div_one] at hτ'
  exact hτ'.symm

/-! ## The contraction -/

/-- The box of a pair of intervals, as a set of pairs. -/
def boxSet (T : Iv × Iv) : Set (ℝ × ℝ) := {x | T.1.Mem x.1 ∧ T.2.Mem x.2}

lemma mem_boxSet {T : Iv × Iv} {x : ℝ × ℝ} : x ∈ boxSet T ↔ T.1.Mem x.1 ∧ T.2.Mem x.2 := Iff.rfl

/-- The preconditioned equations `G = P F`, `P ≈ F'(x*)⁻¹`. -/
def G1E : IE := k (-336 / 1000) * QE + k (-63 / 1000) * RE

def G2E : IE := k (-245 / 1000) * QE + k (-1161 / 1000) * RE

/-- The simplified Newton map `T(x) = x − G(x)`. -/
def Tmap (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.1 - G1E.eval (envOf x.1 x.2), x.2 - G2E.eval (envOf x.1 x.2))

/-- The contraction estimate on a box: `|1 − ∂φG₁| + |∂θG₁| ≤ 1/2` and
`|∂φG₂| + |1 − ∂θG₂| ≤ 1/2`, with the partial derivatives enclosed on the box. -/
def contrOK (T : Iv × Iv) : Bool :=
  decide (2 * ((Iv.sub ⟨S, S⟩ ((G1E.diff dφ).ieval (boxOf T.1.lo T.1.hi T.2.lo T.2.hi))).mag
      + ((G1E.diff dθ).ieval (boxOf T.1.lo T.1.hi T.2.lo T.2.hi)).mag) ≤ S)
  && decide (2 * (((G2E.diff dφ).ieval (boxOf T.1.lo T.1.hi T.2.lo T.2.hi)).mag
      + (Iv.sub ⟨S, S⟩ ((G2E.diff dθ).ieval (boxOf T.1.lo T.1.hi T.2.lo T.2.hi))).mag) ≤ S)

/-- **The computation**: the contraction estimate on the target box. -/
theorem contrOK_target : contrOK target = true := by
  decide +kernel

lemma half_of_le {a b : ℤ} (h : 2 * (a + b) ≤ S) : (a : ℝ) / S + (b : ℝ) / S ≤ 1 / 2 := by
  have hS := S_pos
  rw [← add_div, div_le_iff₀ hS]
  have : ((2 * (a + b) : ℤ) : ℝ) ≤ S := by exact_mod_cast h
  push_cast at this
  linarith

lemma abs_sub_le_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)

lemma abs_lin_le {h₁ h₂ α β a b m : ℝ} (hα : |α| ≤ a) (hβ : |β| ≤ b) (hm₁ : |h₁| ≤ m)
    (hm₂ : |h₂| ≤ m) (hab : a + b ≤ 1 / 2) : |h₁ * α + h₂ * β| ≤ m / 2 := by
  have hm : 0 ≤ m := (abs_nonneg _).trans hm₁
  calc |h₁ * α + h₂ * β| ≤ |h₁| * |α| + |h₂| * |β| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ m * a + m * b := by
        gcongr
    _ ≤ m / 2 := by nlinarith

/-- **Soundness of the contraction check**: on the box, `T` is `1/2`-Lipschitz for the max-norm,
coordinate by coordinate. -/
theorem lip_of_contrOK {T : Iv × Iv} (hc : contrOK T = true) {x y : ℝ × ℝ}
    (hx : x ∈ boxSet T) (hy : y ∈ boxSet T) :
    |(Tmap x).1 - (Tmap y).1| ≤ max |x.1 - y.1| |x.2 - y.2| / 2 ∧
    |(Tmap x).2 - (Tmap y).2| ≤ max |x.1 - y.1| |x.2 - y.2| / 2 := by
  unfold contrOK at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hc1, hc2⟩ := hc
  have hm1 : |x.1 - y.1| ≤ max |x.1 - y.1| |x.2 - y.2| := le_max_left _ _
  have hm2 : |x.2 - y.2| ≤ max |x.1 - y.1| |x.2 - y.2| := le_max_right _ _
  have hz : ∀ τ ∈ Ioo (0 : ℝ) 1, ∀ i, (boxOf T.1.lo T.1.hi T.2.lo T.2.hi i).Mem
      (lineEnv y x τ i) := fun τ hτ =>
    mem_boxOf (Iv.mem_line hy.1 hx.1 hτ.1.le hτ.2.le) (Iv.mem_line hy.2 hx.2 hτ.1.le hτ.2.le)
  constructor
  · obtain ⟨τ, hτ, he⟩ := IE_mvt G1E x y
    have hp := Iv.abs_le_mag (Iv.mem_sub Iv.mem_one (IE.mem_ieval (hz τ hτ) (G1E.diff dφ)))
    have hq := Iv.abs_le_mag (IE.mem_ieval (hz τ hτ) (G1E.diff dθ))
    rw [← abs_neg] at hq
    have key : (Tmap x).1 - (Tmap y).1
        = (x.1 - y.1) * (1 - (G1E.diff dφ).eval (lineEnv y x τ))
          + (x.2 - y.2) * -(G1E.diff dθ).eval (lineEnv y x τ) := by
      simp only [Tmap]
      linear_combination -he
    rw [key]
    exact abs_lin_le hp hq hm1 hm2 (half_of_le hc1)
  · obtain ⟨τ, hτ, he⟩ := IE_mvt G2E x y
    have hp := Iv.abs_le_mag (IE.mem_ieval (hz τ hτ) (G2E.diff dφ))
    rw [← abs_neg] at hp
    have hq := Iv.abs_le_mag (Iv.mem_sub Iv.mem_one (IE.mem_ieval (hz τ hτ) (G2E.diff dθ)))
    have key : (Tmap x).2 - (Tmap y).2
        = (x.1 - y.1) * -(G2E.diff dφ).eval (lineEnv y x τ)
          + (x.2 - y.2) * (1 - (G2E.diff dθ).eval (lineEnv y x τ)) := by
      simp only [Tmap]
      linear_combination -he
    rw [key]
    exact abs_lin_le hp hq hm1 hm2 (half_of_le hc2)

/-- Zeros of `F` are fixed points of `T`. -/
lemma fixed_of_zero {x : ℝ × ℝ} (hQ : QE.eval (envOf x.1 x.2) = 0)
    (hR : RE.eval (envOf x.1 x.2) = 0) : Tmap x = x := by
  simp only [Tmap, G1E, G2E, k, IE.eval_add', IE.eval_mul', IE.eval_c, hQ, hR, mul_zero,
    add_zero, sub_zero, Prod.mk.eta]

/-- Fixed points of `T` are zeros of `F` (`P` is invertible). -/
lemma zero_of_fixed {x : ℝ × ℝ} (h : Tmap x = x) :
    QE.eval (envOf x.1 x.2) = 0 ∧ RE.eval (envOf x.1 x.2) = 0 := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [Tmap, G1E, G2E, k, IE.eval_add', IE.eval_mul', IE.eval_c] at h1 h2
  push_cast at h1 h2
  constructor <;> linarith

/-- **Uniqueness**: `T` has at most one fixed point in the target box. -/
theorem fixed_unique {x y : ℝ × ℝ} (hx : x ∈ boxSet target) (hy : y ∈ boxSet target)
    (hfx : Tmap x = x) (hfy : Tmap y = y) : x = y := by
  obtain ⟨h1, h2⟩ := lip_of_contrOK contrOK_target hx hy
  rw [hfx, hfy] at h1 h2
  have hm : max |x.1 - y.1| |x.2 - y.2| ≤ 0 := by
    have := max_le h1 h2
    linarith
  have e1 : |x.1 - y.1| = 0 := le_antisymm ((le_max_left _ _).trans hm) (abs_nonneg _)
  have e2 : |x.2 - y.2| = 0 := le_antisymm ((le_max_right _ _).trans hm) (abs_nonneg _)
  exact Prod.ext (sub_eq_zero.1 (abs_eq_zero.1 e1)) (sub_eq_zero.1 (abs_eq_zero.1 e2))

/-! ## Existence: Banach's fixed-point theorem on the tight box -/

/-- The tight box: half-width `2¹⁰` units, i.e. `2⁻³⁰ ≈ 9.3 · 10⁻¹⁰`. -/
def tbox : Iv × Iv := (⟨cφ₀ - 1024, cφ₀ + 1024⟩, ⟨cθ₀ - 1024, cθ₀ + 1024⟩)

/-- `|G(center)| ≤ 2⁻⁴¹ = (1 − 1/2) · 2⁻³⁰` in both coordinates. -/
def mapOK : Bool :=
  decide (2 * (G1E.ieval (boxOf cφ₀ cφ₀ cθ₀ cθ₀)).mag ≤ 1024)
    && decide (2 * (G2E.ieval (boxOf cφ₀ cφ₀ cθ₀ cθ₀)).mag ≤ 1024)

/-- **The computation**: the residual at the center. -/
theorem mapOK_true : mapOK = true := by
  decide +kernel

lemma tbox_sub : boxSet tbox ⊆ boxSet target := by
  have hS := S_pos
  have c1 : cφ₀ - rad ≤ cφ₀ - 1024 := by unfold rad; omega
  have c2 : cφ₀ + 1024 ≤ cφ₀ + rad := by unfold rad; omega
  have c3 : cθ₀ - rad ≤ cθ₀ - 1024 := by unfold rad; omega
  have c4 : cθ₀ + 1024 ≤ cθ₀ + rad := by unfold rad; omega
  rintro x ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (div_le_div_of_nonneg_right (by exact_mod_cast c1) hS.le).trans h1
  · exact h2.trans (div_le_div_of_nonneg_right (by exact_mod_cast c2) hS.le)
  · exact (div_le_div_of_nonneg_right (by exact_mod_cast c3) hS.le).trans h3
  · exact h4.trans (div_le_div_of_nonneg_right (by exact_mod_cast c4) hS.le)

lemma le_half_of_two_mul_le {a r : ℤ} (h : 2 * a ≤ r) : (a : ℝ) / S ≤ (r : ℝ) / S / 2 := by
  have hS := S_pos
  have h' : ((2 * a : ℤ) : ℝ) ≤ r := by exact_mod_cast h
  push_cast at h'
  rw [show (r : ℝ) / S / 2 = ((r : ℝ) / 2) / S by ring]
  exact div_le_div_of_nonneg_right (by linarith) hS.le

/-- The center of the tight box. -/
def ctr : ℝ × ℝ := ((cφ₀ : ℝ) / S, (cθ₀ : ℝ) / S)

lemma ctr_mem : ctr ∈ boxSet tbox := by
  have hS := S_pos
  refine mem_boxSet.2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    refine div_le_div_of_nonneg_right ?_ hS.le <;> simp only [tbox] <;> push_cast <;> linarith

/-- Membership in a box of half-width `r` around `c`, as a distance bound. -/
lemma mem_iff_abs {c r : ℤ} {x : ℝ} :
    Iv.Mem ⟨c - r, c + r⟩ x ↔ |x - (c : ℝ) / S| ≤ (r : ℝ) / S := by
  have hS := S_pos
  unfold Iv.Mem
  rw [abs_le]
  push_cast
  rw [sub_div, add_div]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **`T` maps the tight box into itself.** -/
theorem maps_tbox : MapsTo Tmap (boxSet tbox) (boxSet tbox) := by
  intro x hx
  have hS := S_pos
  have hmap := mapOK_true
  unfold mapOK at hmap
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hmap
  obtain ⟨hm1, hm2⟩ := hmap
  have hcb : ∀ i, (boxOf cφ₀ cφ₀ cθ₀ cθ₀ i).Mem (envOf ctr.1 ctr.2 i) :=
    mem_boxOf ⟨le_rfl, le_rfl⟩ ⟨le_rfl, le_rfl⟩
  have hg1 := Iv.abs_le_mag (IE.mem_ieval hcb G1E)
  have hg2 := Iv.abs_le_mag (IE.mem_ieval hcb G2E)
  have hm1' := le_half_of_two_mul_le hm1
  have hm2' := le_half_of_two_mul_le hm2
  push_cast at hm1' hm2'
  obtain ⟨hl1, hl2⟩ := lip_of_contrOK contrOK_target (tbox_sub hx) (tbox_sub ctr_mem)
  have hx1 : |x.1 - ctr.1| ≤ (1024 : ℝ) / S := by
    have := mem_iff_abs.1 hx.1; push_cast at this; exact this
  have hx2 : |x.2 - ctr.2| ≤ (1024 : ℝ) / S := by
    have := mem_iff_abs.1 hx.2; push_cast at this; exact this
  have hmax : max |x.1 - ctr.1| |x.2 - ctr.2| ≤ (1024 : ℝ) / S := max_le hx1 hx2
  refine mem_boxSet.2 ⟨mem_iff_abs.2 ?_, mem_iff_abs.2 ?_⟩
  · push_cast
    have e : (Tmap x).1 - (cφ₀ : ℝ) / S
        = ((Tmap x).1 - (Tmap ctr).1) - G1E.eval (envOf ctr.1 ctr.2) := by
      simp only [Tmap, ctr]; ring
    rw [e]
    calc _ ≤ |(Tmap x).1 - (Tmap ctr).1| + |G1E.eval (envOf ctr.1 ctr.2)| := abs_sub_le_add_abs _ _
      _ ≤ (1024 : ℝ) / S / 2 + (1024 : ℝ) / S / 2 := by
          gcongr
          · exact hl1.trans (by linarith)
          · exact hg1.trans hm1'
      _ = (1024 : ℝ) / S := by ring
  · push_cast
    have e : (Tmap x).2 - (cθ₀ : ℝ) / S
        = ((Tmap x).2 - (Tmap ctr).2) - G2E.eval (envOf ctr.1 ctr.2) := by
      simp only [Tmap, ctr]; ring
    rw [e]
    calc _ ≤ |(Tmap x).2 - (Tmap ctr).2| + |G2E.eval (envOf ctr.1 ctr.2)| := abs_sub_le_add_abs _ _
      _ ≤ (1024 : ℝ) / S / 2 + (1024 : ℝ) / S / 2 := by
          gcongr
          · exact hl2.trans (by linarith)
          · exact hg2.trans hm2'
      _ = (1024 : ℝ) / S := by ring

lemma isClosed_boxSet (T : Iv × Iv) : IsClosed (boxSet T) := by
  have h1 : IsClosed {x : ℝ × ℝ | (T.1.lo : ℝ) / S ≤ x.1 ∧ x.1 ≤ (T.1.hi : ℝ) / S} :=
    (isClosed_le continuous_const continuous_fst).inter (isClosed_le continuous_fst continuous_const)
  have h2 : IsClosed {x : ℝ × ℝ | (T.2.lo : ℝ) / S ≤ x.2 ∧ x.2 ≤ (T.2.hi : ℝ) / S} :=
    (isClosed_le continuous_const continuous_snd).inter (isClosed_le continuous_snd continuous_const)
  exact h1.inter h2

/-- **Existence** (Banach's fixed-point theorem): `T` has a fixed point in the tight box. -/
theorem exists_fixed : ∃ x ∈ boxSet tbox, Tmap x = x := by
  have hsc : IsComplete (boxSet tbox) := (isClosed_boxSet tbox).isComplete
  have hK : ContractingWith (1 / 2 : NNReal)
      (maps_tbox.restrict Tmap (boxSet tbox) (boxSet tbox)) := by
    refine ⟨by simpa using NNReal.half_lt_self (a := 1) one_ne_zero, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun p q => ?_
    obtain ⟨h1, h2⟩ := lip_of_contrOK contrOK_target (tbox_sub p.2) (tbox_sub q.2)
    simp only [Subtype.dist_eq, MapsTo.val_restrict_apply, Prod.dist_eq, Real.dist_eq]
    push_cast
    rw [max_le_iff]
    constructor <;> linarith
  obtain ⟨x, hx, hfix, -⟩ := hK.exists_fixedPoint' hsc maps_tbox ctr_mem (edist_ne_top _ _)
  exact ⟨x, hx, hfix⟩

/-! ## The solution of Romik's system -/

/-- Positivity of `3 cos φ − cos θ`, `N₁`, `κ`, `c₀` on the target box. -/
def posOK : Bool :=
  decide (0 < (denE.ieval (boxOf target.1.lo target.1.hi target.2.lo target.2.hi)).lo)
    && decide (0 < (N1E.ieval (boxOf target.1.lo target.1.hi target.2.lo target.2.hi)).lo)
    && decide (0 < (kkE.ieval (boxOf target.1.lo target.1.hi target.2.lo target.2.hi)).lo)
    && decide (0 < (c0E.ieval (boxOf target.1.lo target.1.hi target.2.lo target.2.hi)).lo)

theorem posOK_true : posOK = true := by
  decide +kernel

lemma pos_of_lo {x : ℝ} {I : Iv} (hx : I.Mem x) (h : 0 < I.lo) : 0 < x :=
  (div_pos (by exact_mod_cast h) S_pos).trans_le hx.1

lemma pos_on_target {φ θ : ℝ} (hx : (φ, θ) ∈ boxSet target) :
    0 < denE.eval (envOf φ θ) ∧ 0 < N1E.eval (envOf φ θ) ∧ 0 < kkE.eval (envOf φ θ)
      ∧ 0 < c0E.eval (envOf φ θ) := by
  have h := posOK_true
  unfold posOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hb := mem_boxOf (φ := φ) (θ := θ) hx.1 hx.2
  exact ⟨pos_of_lo (IE.mem_ieval hb denE) h1, pos_of_lo (IE.mem_ieval hb N1E) h2,
    pos_of_lo (IE.mem_ieval hb kkE) h3, pos_of_lo (IE.mem_ieval hb c0E) h4⟩

lemma denE_eval (φ θ : ℝ) : denE.eval (envOf φ θ) = 3 * Real.cos φ - Real.cos θ := by
  simp only [denE, cφ, cθ, k, IE.eval_sub', IE.eval_mul', IE.eval_v, IE.eval_c, envOf]
  push_cast
  ring

/-- The target box lies in `0 < φ < θ ≤ π/4`. -/
lemma target_angles {φ θ : ℝ} (hx : (φ, θ) ∈ boxSet target) : 0 < φ ∧ φ < θ ∧ θ ≤ π / 4 := by
  have hS := S_pos
  have hpi := Real.pi_gt_d2
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hx
  have c1 : (0 : ℤ) < cφ₀ - rad := by norm_num [cφ₀, rad]
  have c2 : cφ₀ + rad < cθ₀ - rad := by norm_num [cφ₀, cθ₀, rad]
  have c3 : 100 * (cθ₀ + rad) ≤ 78 * S := by norm_num [cθ₀, rad, S]
  simp only [target] at h1 h2 h3 h4
  refine ⟨(div_pos (by exact_mod_cast c1) hS).trans_le h1, ?_, ?_⟩
  · exact h2.trans_lt ((div_lt_div_of_pos_right (by exact_mod_cast c2) hS).trans_le h3)
  · have : ((cθ₀ + rad : ℤ) : ℝ) / S ≤ 78 / 100 := by
      rw [div_le_iff₀ hS]
      have := (Int.cast_le (R := ℝ)).2 c3
      push_cast at this ⊢
      linarith
    push_cast at this h4
    linarith

/-- From a zero of `F` in the target box, `A = N₁ / (3 cos φ − cos θ)` and `B = A κ + c₀` solve
Romik's system. -/
theorem spec_of_zero {φ θ : ℝ} (hx : (φ, θ) ∈ boxSet target) (hQ : QE.eval (envOf φ θ) = 0)
    (hR : RE.eval (envOf φ θ) = 0) :
    Spec (N1E.eval (envOf φ θ) / denE.eval (envOf φ θ))
      (N1E.eval (envOf φ θ) / denE.eval (envOf φ θ) * kkE.eval (envOf φ θ)
        + c0E.eval (envOf φ θ)) φ θ := by
  obtain ⟨hden, hN, hkk, hc0⟩ := pos_on_target hx
  obtain ⟨hφ, hφθ, hθ⟩ := target_angles hx
  set A := N1E.eval (envOf φ θ) / denE.eval (envOf φ θ) with hA_def
  set B := A * kkE.eval (envOf φ θ) + c0E.eval (envOf φ θ) with hB_def
  have hA : 0 ≤ A := (div_pos hN hden).le
  have e13 : eq1 A B φ θ - 2 * eq3 A B φ θ = 0 := by
    rw [eq1_sub_eq3, hA_def, div_mul_cancel₀ _ hden.ne', sub_self]
  have e4 : eq4 A B φ θ = 0 := by rw [eq4_eq, hB_def]; ring
  have hd : 3 * Real.cos φ - Real.cos θ ≠ 0 := by rw [← denE_eval]; exact hden.ne'
  have e3 : eq3 A B φ θ = 0 := by
    have h := QE_eval A B φ θ
    rw [hQ, e13, e4] at h
    have h' : (3 * Real.cos φ - Real.cos θ) * eq3 A B φ θ = 0 := by linear_combination -h
    exact (mul_eq_zero.1 h').resolve_left hd
  have e2 : eq2 A B φ θ = 0 := by
    have h := RE_eval A B φ θ
    rw [hR, e13, e4] at h
    have h' : (3 * Real.cos φ - Real.cos θ) * eq2 A B φ θ = 0 := by linear_combination -h
    exact (mul_eq_zero.1 h').resolve_left hd
  have e1 : eq1 A B φ θ = 0 := by linarith
  exact spec_iff.2 ⟨hφ.le, hφθ.le, hθ, hA, by positivity, e1, e2, e3, e4⟩

/-- **Existence and uniqueness of Gerver's constants**: Romik's system has exactly one solution.
This is the upstream `MovingSofa.GerversSofa.ABφθSpec.existsUnique`. -/
theorem spec_existsUnique :
    ∃! ABφθ : ℝ × ℝ × ℝ × ℝ, Spec ABφθ.1 ABφθ.2.1 ABφθ.2.2.1 ABφθ.2.2.2 := by
  obtain ⟨x, hx, hfix⟩ := exists_fixed
  obtain ⟨hQ, hR⟩ := zero_of_fixed hfix
  have hxT := tbox_sub hx
  refine ⟨(N1E.eval (envOf x.1 x.2) / denE.eval (envOf x.1 x.2),
    N1E.eval (envOf x.1 x.2) / denE.eval (envOf x.1 x.2) * kkE.eval (envOf x.1 x.2)
      + c0E.eval (envOf x.1 x.2), x.1, x.2), spec_of_zero (φ := x.1) (θ := x.2) hxT hQ hR, ?_⟩
  rintro ⟨A', B', φ', θ'⟩ h'
  simp only at h'
  have hloc := Spec_mem_target h'
  obtain ⟨hQ', hR'⟩ := QE_RE_eq_zero h'
  have hxy : ((φ', θ') : ℝ × ℝ) = x :=
    fixed_unique (mem_boxSet.2 hloc) hxT (fixed_of_zero (x := (φ', θ')) hQ' hR') hfix
  subst hxy
  obtain ⟨-, -, -, -, -, e1, -, e3, e4⟩ := spec_iff.1 h'
  have hden := (pos_on_target hxT).1
  have e13 := eq1_sub_eq3 A' B' φ' θ'
  rw [e1, e3] at e13
  have hA : A' = N1E.eval (envOf φ' θ') / denE.eval (envOf φ' θ') := by
    rw [eq_div_iff hden.ne']
    linarith
  have hB : B' = N1E.eval (envOf φ' θ') / denE.eval (envOf φ' θ') * kkE.eval (envOf φ' θ')
      + c0E.eval (envOf φ' θ') := by
    have := eq4_eq A' B' φ' θ'
    rw [e4] at this
    rw [← hA]
    linarith
  exact Prod.ext hA (Prod.ext hB rfl)

/-- Every solution of Romik's system has `(φ, θ)` in the tight box. -/
theorem Spec_mem_tbox {A B φ θ : ℝ} (h : Spec A B φ θ) : tbox.1.Mem φ ∧ tbox.2.Mem θ := by
  obtain ⟨x, hx, hfix⟩ := exists_fixed
  have hloc := Spec_mem_target h
  obtain ⟨hQ, hR⟩ := QE_RE_eq_zero h
  have hxy : ((φ, θ) : ℝ × ℝ) = x :=
    fixed_unique (mem_boxSet.2 hloc) (tbox_sub hx) (fixed_of_zero (x := (φ, θ)) hQ hR) hfix
  rw [← hxy] at hx
  exact hx

/-- **Gerver's angles**: every solution of Romik's system has `0 < φ ≤ 1/25` and
`φ < θ < π/4`. -/
theorem Spec_angles {A B φ θ : ℝ} (h : Spec A B φ θ) :
    0 < φ ∧ φ ≤ 1 / 25 ∧ φ < θ ∧ θ < π / 4 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := Spec_mem_tbox h
  have hS := S_pos
  have hpi := Real.pi_gt_d2
  have c1 : (0 : ℤ) < cφ₀ - 1024 := by norm_num [cφ₀]
  have c2 : 25 * (cφ₀ + 1024) ≤ S := by norm_num [cφ₀, S]
  have c3 : cφ₀ + 1024 < cθ₀ - 1024 := by norm_num [cφ₀, cθ₀]
  have c4 : 100 * (cθ₀ + 1024) ≤ 78 * S := by norm_num [cθ₀, S]
  simp only [tbox] at h1 h2 h3 h4
  refine ⟨(div_pos (by exact_mod_cast c1) hS).trans_le h1, ?_, ?_, ?_⟩
  · refine h2.trans ?_
    rw [div_le_iff₀ hS]
    have := (Int.cast_le (R := ℝ)).2 c2
    push_cast at this ⊢
    linarith
  · exact h2.trans_lt ((div_lt_div_of_pos_right (by exact_mod_cast c3) hS).trans_le h3)
  · have : ((cθ₀ + 1024 : ℤ) : ℝ) / S ≤ 78 / 100 := by
      rw [div_le_iff₀ hS]
      have := (Int.cast_le (R := ℝ)).2 c4
      push_cast at this ⊢
      linarith
    push_cast at this h4
    linarith

end Sofa.GC
