/-
# Sofa/GerverConst.lean — localizing Gerver's constants

Gerver's constants `A, B, φ, θ` are defined upstream as the unique solution of Romik's system
(`MovingSofa.GerversSofa.ABφθSpec`, Romik 2018, eq. 1–4).  This file works with a verbatim copy
`Spec` of that system, so that it imports only Mathlib (through `Sofa/IntervalArith.lean`): the
upstream `ABφθSpec.existsUnique` is proved from it (`Sofa/GerverUnique.lean`).

We prove, **for every solution** of the system, that `(φ, θ)` lies in the box

    |φ − 0.0391773648| ≤ 2⁻²⁹ ≈ 0.00195,   |θ − 0.6813015094| ≤ 2⁻²⁹

(`Spec_mem_target`), by a verified branch-and-bound computation.

* `A` is eliminated by `E₁ − 2E₃` (its coefficient `3 cos φ − cos θ` is positive) and `B` by
  `E₄`; what remains are two equations `Q̃(φ, θ) = 0`, `R̃(φ, θ) = 0` (`QE`, `RE`).  The identities
  `QE_eval`, `RE_eval`, `eq1_sub_eq3`, `eq4_eq` hold for all `A`, `B`, so they serve both for
  necessity (`QE_RE_eq_zero`) and for the construction of a solution (`GerverUnique.lean`).
* `check` subdivides `[0, 0.8]²` (which contains the triangle `0 ≤ φ ≤ θ ≤ π/4`) and discards a box
  when it lies below the diagonal, inside the target, or when `Q̃` or `R̃` has a constant sign on it
  (interval arithmetic with `sin`, `cos` enclosed by Taylor polynomials, `π` by Mathlib's 20-digit
  bounds).  `check_sound` is the soundness theorem; `check_top` is the computation, checked by the
  kernel (`decide +kernel`).

STATUS: [PROOF-C-local] round 36–37 (2026-09-23, Opus 5.5).
-/
import Sofa.IntervalArith

noncomputable section

open Real Set

/- The kernel checks below are run one after the other: with asynchronous elaboration the memory
of the finished checks is retained until the end of the file (about 1 MB per box). -/
set_option Elab.async false

namespace Sofa.GC

open IA

/-! ## Romik's system -/

/-- Romik's system for Gerver's constants (Romik 2018, eq. 1–4): a verbatim copy of the upstream
`MovingSofa.GerversSofa.ABφθSpec`, to which it is definitionally equal. -/
def Spec (A B φ θ : ℝ) : Prop :=
  0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
  A * (θ.cos - φ.cos) - 2 * B * φ.sin
    + (θ - φ - 1) * θ.cos - θ.sin + φ.cos + φ.sin = 0 ∧
  A * (3 * θ.sin + φ.sin) - 2 * B * φ.cos
    + 3 * (θ - φ - 1) * θ.sin + 3 * θ.cos - φ.sin + φ.cos = 0 ∧
  A * φ.cos - (φ.sin + 1 / 2 - φ.cos / 2 + B * φ.sin) = 0 ∧
  (A + π / 2 - φ - θ) - (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4) = 0

/-- The left-hand sides of the four equations. -/
def eq1 (A B φ θ : ℝ) : ℝ :=
  A * (θ.cos - φ.cos) - 2 * B * φ.sin + (θ - φ - 1) * θ.cos - θ.sin + φ.cos + φ.sin

def eq2 (A B φ θ : ℝ) : ℝ :=
  A * (3 * θ.sin + φ.sin) - 2 * B * φ.cos + 3 * (θ - φ - 1) * θ.sin + 3 * θ.cos - φ.sin + φ.cos

def eq3 (A B φ _θ : ℝ) : ℝ := A * φ.cos - (φ.sin + 1 / 2 - φ.cos / 2 + B * φ.sin)

def eq4 (A B φ θ : ℝ) : ℝ := (A + π / 2 - φ - θ) - (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4)

lemma spec_iff {A B φ θ : ℝ} : Spec A B φ θ ↔ 0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
    eq1 A B φ θ = 0 ∧ eq2 A B φ θ = 0 ∧ eq3 A B φ θ = 0 ∧ eq4 A B φ θ = 0 := Iff.rfl

/-! ## The reduced equations -/

/-- Variables: `0 ↦ φ`, `1 ↦ θ`, `2 ↦ π`, `3 ↦ sin φ`, `4 ↦ cos φ`, `5 ↦ sin θ`, `6 ↦ cos θ`. -/
def vφ : IE := .v 0
def vθ : IE := .v 1
def vπ : IE := .v 2
def sφ : IE := .v 3
def cφ : IE := .v 4
def sθ : IE := .v 5
def cθ : IE := .v 6
def k (q : ℚ) : IE := .c q

def dE : IE := vθ - vφ
def N1E : IE := dE * cθ + k 3 * sφ - sθ - cθ + k 1
def denE : IE := k 3 * cφ - cθ
def kkE : IE := k 1 + dE * k (1 / 2)
def c0E : IE := vπ * k (1 / 2) - vφ - vθ + dE * k (1 / 2) + dE * dE * k (1 / 4)

/-- `Q̃ = N₁ (cos φ − sin φ · κ) − (3 cos φ − cos θ)(sin φ + ½ − ½ cos φ + sin φ · c₀)`. -/
def QE : IE := N1E * (cφ - sφ * kkE) - denE * (sφ + k (1 / 2) - cφ * k (1 / 2) + sφ * c0E)

/-- `R̃ = N₁ (3 sin θ + sin φ − 2 cos φ · κ) + (3 cos φ − cos θ)(3(θ − φ − 1) sin θ + 3 cos θ
− sin φ + cos φ − 2 cos φ · c₀)`. -/
def RE : IE := N1E * (k 3 * sθ + sφ - k 2 * cφ * kkE)
  + denE * (k 3 * (dE - k 1) * sθ + k 3 * cθ - sφ + cφ - k 2 * cφ * c0E)

/-- The values of the variables. -/
def envOf (φ θ : ℝ) : ℕ → ℝ
  | 0 => φ
  | 1 => θ
  | 2 => π
  | 3 => Real.sin φ
  | 4 => Real.cos φ
  | 5 => Real.sin θ
  | 6 => Real.cos θ
  | _ => 0

/-- `E₁ − 2E₃ = N₁ − A (3 cos φ − cos θ)`: this eliminates `B`. -/
lemma eq1_sub_eq3 (A B φ θ : ℝ) :
    eq1 A B φ θ - 2 * eq3 A B φ θ = N1E.eval (envOf φ θ) - A * denE.eval (envOf φ θ) := by
  simp only [eq1, eq3, N1E, denE, dE, vφ, vθ, sφ, cφ, sθ, cθ, k, IE.eval_add', IE.eval_sub',
    IE.eval_mul', IE.eval_v, IE.eval_c, envOf]
  push_cast
  ring

/-- `E₄ = A κ + c₀ − B`. -/
lemma eq4_eq (A B φ θ : ℝ) :
    eq4 A B φ θ = A * kkE.eval (envOf φ θ) + c0E.eval (envOf φ θ) - B := by
  simp only [eq4, kkE, c0E, dE, vφ, vθ, vπ, k, IE.eval_add', IE.eval_sub', IE.eval_mul',
    IE.eval_v, IE.eval_c, envOf]
  push_cast
  ring

/-- `Q̃` as a combination of the equations, for all `A`, `B`. -/
lemma QE_eval (A B φ θ : ℝ) : QE.eval (envOf φ θ) =
    (3 * Real.cos φ - Real.cos θ) * (eq3 A B φ θ - Real.sin φ * eq4 A B φ θ)
      + (Real.cos φ - Real.sin φ * (1 + (θ - φ) / 2)) * (eq1 A B φ θ - 2 * eq3 A B φ θ) := by
  simp only [QE, N1E, denE, kkE, c0E, dE, vφ, vθ, vπ, sφ, cφ, sθ, cθ, k, IE.eval_add',
    IE.eval_sub', IE.eval_mul', IE.eval_v, IE.eval_c, envOf, eq1, eq3, eq4]
  push_cast
  ring

/-- `R̃` as a combination of the equations, for all `A`, `B`. -/
lemma RE_eval (A B φ θ : ℝ) : RE.eval (envOf φ θ) =
    (3 * Real.cos φ - Real.cos θ) * (eq2 A B φ θ - 2 * Real.cos φ * eq4 A B φ θ)
      + (3 * Real.sin θ + Real.sin φ - 2 * Real.cos φ * (1 + (θ - φ) / 2))
        * (eq1 A B φ θ - 2 * eq3 A B φ θ) := by
  simp only [RE, N1E, denE, kkE, c0E, dE, vφ, vθ, vπ, sφ, cφ, sθ, cθ, k, IE.eval_add',
    IE.eval_sub', IE.eval_mul', IE.eval_v, IE.eval_c, envOf, eq1, eq2, eq3, eq4]
  push_cast
  ring

/-- `A` and `B` eliminated: every solution of Romik's system satisfies `Q̃ = R̃ = 0`. -/
theorem QE_RE_eq_zero {A B φ θ : ℝ} (h : Spec A B φ θ) :
    QE.eval (envOf φ θ) = 0 ∧ RE.eval (envOf φ θ) = 0 := by
  obtain ⟨-, -, -, -, -, e1, e2, e3, e4⟩ := spec_iff.1 h
  rw [QE_eval A B, RE_eval A B, e1, e2, e3, e4]
  constructor <;> ring

/-! ## Boxes -/

/-- An enclosure of `π` (Mathlib's 20-digit bounds, rounded outward to the grid). -/
def piIv : Iv := ⟨qdn (314159265358979323846 / 100000000000000000000),
  qup (314159265358979323847 / 100000000000000000000)⟩

lemma mem_piIv : piIv.Mem π := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  refine ⟨(qdn_le _).trans ?_, ?_⟩
  · push_cast; norm_num at h1 ⊢; linarith
  · refine le_trans ?_ (le_qup _)
    push_cast; norm_num at h2 ⊢; linarith

/-- The box of the variables over `[fl, fh] × [tl, th]`. -/
def boxOf (fl fh tl th : ℤ) : ℕ → Iv
  | 0 => ⟨fl, fh⟩
  | 1 => ⟨tl, th⟩
  | 2 => piIv
  | 3 => Iv.sin ⟨fl, fh⟩
  | 4 => Iv.cos ⟨fl, fh⟩
  | 5 => Iv.sin ⟨tl, th⟩
  | 6 => Iv.cos ⟨tl, th⟩
  | _ => ⟨0, 0⟩

lemma mem_boxOf {φ θ : ℝ} {fl fh tl th : ℤ} (hφ : Iv.Mem ⟨fl, fh⟩ φ) (hθ : Iv.Mem ⟨tl, th⟩ θ) :
    ∀ i, (boxOf fl fh tl th i).Mem (envOf φ θ i)
  | 0 => hφ
  | 1 => hθ
  | 2 => mem_piIv
  | 3 => Iv.mem_sin hφ
  | 4 => Iv.mem_cos hφ
  | 5 => Iv.mem_sin hθ
  | 6 => Iv.mem_cos hθ
  | _ + 7 => by
    show ((0 : ℤ) : ℝ) / S ≤ 0 ∧ (0 : ℝ) ≤ ((0 : ℤ) : ℝ) / S
    simp

/-! ## The branch-and-bound check -/

/-- A box is discarded if it lies strictly below the diagonal `θ = φ`, inside the target, or if
`Q̃` or `R̃` has a constant sign on it. -/
def leaf (T : Iv × Iv) (fl fh tl th : ℤ) : Bool :=
  decide (th < fl)
    || (decide (T.1.lo ≤ fl) && decide (fh ≤ T.1.hi) && decide (T.2.lo ≤ tl)
      && decide (th ≤ T.2.hi))
    || (QE.ieval (boxOf fl fh tl th)).nonzero || (RE.ieval (boxOf fl fh tl th)).nonzero

/-- Branch and bound: discard the box or split it into four. -/
def check (T : Iv × Iv) : ℕ → ℤ → ℤ → ℤ → ℤ → Bool
  | 0, fl, fh, tl, th => leaf T fl fh tl th
  | d + 1, fl, fh, tl, th =>
    leaf T fl fh tl th
      || (check T d fl ((fl + fh) / 2) tl ((tl + th) / 2)
        && check T d fl ((fl + fh) / 2) ((tl + th) / 2) th
        && check T d ((fl + fh) / 2) fh tl ((tl + th) / 2)
        && check T d ((fl + fh) / 2) fh ((tl + th) / 2) th)

lemma leaf_sound {T : Iv × Iv} {fl fh tl th : ℤ} (hc : leaf T fl fh tl th = true) {φ θ : ℝ}
    (hφ : Iv.Mem ⟨fl, fh⟩ φ) (hθ : Iv.Mem ⟨tl, th⟩ θ) (hφθ : φ ≤ θ)
    (hQ : QE.eval (envOf φ θ) = 0) (hR : RE.eval (envOf φ θ) = 0) :
    T.1.Mem φ ∧ T.2.Mem θ := by
  have hS := S_pos
  have hbox := mem_boxOf hφ hθ
  unfold leaf at hc
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ((h | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩) | h) | h
  · exfalso
    have : (th : ℝ) / S < (fl : ℝ) / S := div_lt_div_of_pos_right (by exact_mod_cast h) hS
    have := hθ.2.trans_lt (this.trans_le hφ.1)
    linarith
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact (div_le_div_of_nonneg_right (by exact_mod_cast h1) hS.le).trans hφ.1
    · exact hφ.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast h2) hS.le)
    · exact (div_le_div_of_nonneg_right (by exact_mod_cast h3) hS.le).trans hθ.1
    · exact hθ.2.trans (div_le_div_of_nonneg_right (by exact_mod_cast h4) hS.le)
  · exact absurd hQ (Iv.ne_zero_of_nonzero (IE.mem_ieval hbox QE) h)
  · exact absurd hR (Iv.ne_zero_of_nonzero (IE.mem_ieval hbox RE) h)

/-- **Soundness of the branch and bound.** -/
theorem check_sound (T : Iv × Iv) :
    ∀ (d : ℕ) (fl fh tl th : ℤ), check T d fl fh tl th = true → ∀ {φ θ : ℝ},
      Iv.Mem ⟨fl, fh⟩ φ → Iv.Mem ⟨tl, th⟩ θ → φ ≤ θ →
      QE.eval (envOf φ θ) = 0 → RE.eval (envOf φ θ) = 0 → T.1.Mem φ ∧ T.2.Mem θ
  | 0, fl, fh, tl, th, hc, _, _, hφ, hθ, hφθ, hQ, hR => leaf_sound hc hφ hθ hφθ hQ hR
  | d + 1, fl, fh, tl, th, hc, φ, θ, hφ, hθ, hφθ, hQ, hR => by
    unfold check at hc
    rcases Bool.or_eq_true_iff.1 hc with h | h
    · exact leaf_sound h hφ hθ hφθ hQ hR
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    have hS := S_pos
    set fm := (fl + fh) / 2
    set tm := (tl + th) / 2
    rcases le_total φ ((fm : ℝ) / S) with hf | hf <;> rcases le_total θ ((tm : ℝ) / S) with ht | ht
    · exact check_sound T d fl fm tl tm h1 ⟨hφ.1, hf⟩ ⟨hθ.1, ht⟩ hφθ hQ hR
    · exact check_sound T d fl fm tm th h2 ⟨hφ.1, hf⟩ ⟨ht, hθ.2⟩ hφθ hQ hR
    · exact check_sound T d fm fh tl tm h3 ⟨hf, hφ.2⟩ ⟨hθ.1, ht⟩ hφθ hQ hR
    · exact check_sound T d fm fh tm th h4 ⟨hf, hφ.2⟩ ⟨ht, hθ.2⟩ hφθ hQ hR

/-- Center of the target box, in units of `2⁻⁴⁰`: `φ₀ ≈ 0.0391773648`. -/
def cφ₀ : ℤ := 43075968132

/-- Center of the target box, in units of `2⁻⁴⁰`: `θ₀ ≈ 0.6813015094`. -/
def cθ₀ : ℤ := 749098931588

/-- Half-width of the target box, in units of `2⁻⁴⁰`: `2³¹`, i.e. `2⁻⁹ ≈ 0.00195`. -/
def rad : ℤ := 2147483648

/-- The target box `[φ₀ − 2⁻⁹, φ₀ + 2⁻⁹] × [θ₀ − 2⁻⁹, θ₀ + 2⁻⁹]`. -/
def target : Iv × Iv := (⟨cφ₀ - rad, cφ₀ + rad⟩, ⟨cθ₀ - rad, cθ₀ + rad⟩)

/-- The top box is `[0, top / S]²` with `top / S ≥ 0.8`. -/
def top : ℤ := 879609302221

lemma top_ge : (4 : ℝ) / 5 ≤ (top : ℝ) / S := by
  rw [le_div_iff₀ S_pos]; norm_num [top, S]

/-- One level of the branch and bound, with the midpoints computed. -/
lemma check_succ_of {T : Iv × Iv} {d : ℕ} {fl fh tl th fm tm : ℤ} (hfm : (fl + fh) / 2 = fm)
    (htm : (tl + th) / 2 = tm) (h1 : check T d fl fm tl tm = true)
    (h2 : check T d fl fm tm th = true) (h3 : check T d fm fh tl tm = true)
    (h4 : check T d fm fh tm th = true) : check T (d + 1) fl fh tl th = true := by
  rw [check, hfm, htm, h1, h2, h3, h4]
  simp

/-! ### The computation, in 106 kernel-checked pieces (at most 150 boxes each) -/

theorem ck_0 : check target 15 0 439804651110 0 439804651110 = true := by
  decide +kernel

theorem ck_100 : check target 13 0 109951162777 439804651110 549755813887 = true := by
  decide +kernel

theorem ck_1010 : check target 12 0 54975581388 549755813887 604731395276 = true := by
  decide +kernel

theorem ck_1011 : check target 12 0 54975581388 604731395276 659706976665 = true := by
  decide +kernel

theorem ck_1012 : check target 12 54975581388 109951162777 549755813887 604731395276 = true := by
  decide +kernel

theorem ck_1013 : check target 12 54975581388 109951162777 604731395276 659706976665 = true := by
  decide +kernel

theorem ck_101 : check target 13 0 109951162777 549755813887 659706976665 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_1010 ck_1011 ck_1012 ck_1013

theorem ck_102 : check target 13 109951162777 219902325555 439804651110 549755813887 = true := by
  decide +kernel

theorem ck_103 : check target 13 109951162777 219902325555 549755813887 659706976665 = true := by
  decide +kernel

theorem ck_10 : check target 14 0 219902325555 439804651110 659706976665 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_100 ck_101 ck_102 ck_103

theorem ck_11000 : check target 11 0 27487790694 659706976665 687194767359 = true := by
  decide +kernel

theorem ck_11001 : check target 11 0 27487790694 687194767359 714682558054 = true := by
  decide +kernel

theorem ck_11002 : check target 11 27487790694 54975581388 659706976665 687194767359 = true := by
  decide +kernel

theorem ck_110030 : check target 10 27487790694 41231686041 687194767359 700938662706 = true := by
  decide +kernel

theorem ck_110031 : check target 10 27487790694 41231686041 700938662706 714682558054 = true := by
  decide +kernel

theorem ck_110032 : check target 10 41231686041 54975581388 687194767359 700938662706 = true := by
  decide +kernel

theorem ck_110033 : check target 10 41231686041 54975581388 700938662706 714682558054 = true := by
  decide +kernel

theorem ck_11003 : check target 11 27487790694 54975581388 687194767359 714682558054 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_110030 ck_110031 ck_110032 ck_110033

theorem ck_1100 : check target 12 0 54975581388 659706976665 714682558054 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_11000 ck_11001 ck_11002 ck_11003

theorem ck_11010 : check target 11 0 27487790694 714682558054 742170348748 = true := by
  decide +kernel

theorem ck_11011 : check target 11 0 27487790694 742170348748 769658139443 = true := by
  decide +kernel

theorem ck_110120 : check target 10 27487790694 41231686041 714682558054 728426453401 = true := by
  decide +kernel

theorem ck_110121 : check target 10 27487790694 41231686041 728426453401 742170348748 = true := by
  decide +kernel

theorem ck_110122 : check target 10 41231686041 54975581388 714682558054 728426453401 = true := by
  decide +kernel

theorem ck_1101230 : check target 9 41231686041 48103633714 728426453401 735298401074 = true := by
  decide +kernel

theorem ck_11012310 : check target 8 41231686041 44667659877 735298401074 738734374911 = true := by
  decide +kernel

theorem ck_110123110 : check target 7 41231686041 42949672959 738734374911 740452361829 = true := by
  decide +kernel

theorem ck_110123111 : check target 7 41231686041 42949672959 740452361829 742170348748 = true := by
  decide +kernel

theorem ck_110123112 : check target 7 42949672959 44667659877 738734374911 740452361829 = true := by
  decide +kernel

theorem ck_110123113 : check target 7 42949672959 44667659877 740452361829 742170348748 = true := by
  decide +kernel

theorem ck_11012311 : check target 8 41231686041 44667659877 738734374911 742170348748 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_110123110 ck_110123111 ck_110123112 ck_110123113

theorem ck_11012312 : check target 8 44667659877 48103633714 735298401074 738734374911 = true := by
  decide +kernel

theorem ck_11012313 : check target 8 44667659877 48103633714 738734374911 742170348748 = true := by
  decide +kernel

theorem ck_1101231 : check target 9 41231686041 48103633714 735298401074 742170348748 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_11012310 ck_11012311 ck_11012312 ck_11012313

theorem ck_1101232 : check target 9 48103633714 54975581388 728426453401 735298401074 = true := by
  decide +kernel

theorem ck_1101233 : check target 9 48103633714 54975581388 735298401074 742170348748 = true := by
  decide +kernel

theorem ck_110123 : check target 10 41231686041 54975581388 728426453401 742170348748 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_1101230 ck_1101231 ck_1101232 ck_1101233

theorem ck_11012 : check target 11 27487790694 54975581388 714682558054 742170348748 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_110120 ck_110121 ck_110122 ck_110123

theorem ck_110130 : check target 10 27487790694 41231686041 742170348748 755914244095 = true := by
  decide +kernel

theorem ck_110131 : check target 10 27487790694 41231686041 755914244095 769658139443 = true := by
  decide +kernel

theorem ck_110132000 : check target 7 41231686041 42949672959 742170348748 743888335666 = true := by
  decide +kernel

theorem ck_110132001 : check target 7 41231686041 42949672959 743888335666 745606322584 = true := by
  decide +kernel

theorem ck_110132002 : check target 7 42949672959 44667659877 742170348748 743888335666 = true := by
  decide +kernel

theorem ck_110132003 : check target 7 42949672959 44667659877 743888335666 745606322584 = true := by
  decide +kernel

theorem ck_11013200 : check target 8 41231686041 44667659877 742170348748 745606322584 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_110132000 ck_110132001 ck_110132002 ck_110132003

theorem ck_110132010 : check target 7 41231686041 42949672959 745606322584 747324309502 = true := by
  decide +kernel

theorem ck_110132011 : check target 7 41231686041 42949672959 747324309502 749042296421 = true := by
  decide +kernel

theorem ck_110132012 : check target 7 42949672959 44667659877 745606322584 747324309502 = true := by
  decide +kernel

theorem ck_110132013 : check target 7 42949672959 44667659877 747324309502 749042296421 = true := by
  decide +kernel

theorem ck_11013201 : check target 8 41231686041 44667659877 745606322584 749042296421 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_110132010 ck_110132011 ck_110132012 ck_110132013

theorem ck_11013202 : check target 8 44667659877 48103633714 742170348748 745606322584 = true := by
  decide +kernel

theorem ck_11013203 : check target 8 44667659877 48103633714 745606322584 749042296421 = true := by
  decide +kernel

theorem ck_1101320 : check target 9 41231686041 48103633714 742170348748 749042296421 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_11013200 ck_11013201 ck_11013202 ck_11013203

theorem ck_110132100 : check target 7 41231686041 42949672959 749042296421 750760283339 = true := by
  decide +kernel

theorem ck_110132101 : check target 7 41231686041 42949672959 750760283339 752478270258 = true := by
  decide +kernel

theorem ck_110132102 : check target 7 42949672959 44667659877 749042296421 750760283339 = true := by
  decide +kernel

theorem ck_1101321030 : check target 6 42949672959 43808666418 750760283339 751619276798 = true := by
  decide +kernel

theorem ck_1101321031 : check target 6 42949672959 43808666418 751619276798 752478270258 = true := by
  decide +kernel

theorem ck_1101321032 : check target 6 43808666418 44667659877 750760283339 751619276798 = true := by
  decide +kernel

theorem ck_1101321033 : check target 6 43808666418 44667659877 751619276798 752478270258 = true := by
  decide +kernel

theorem ck_110132103 : check target 7 42949672959 44667659877 750760283339 752478270258 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_1101321030 ck_1101321031 ck_1101321032 ck_1101321033

theorem ck_11013210 : check target 8 41231686041 44667659877 749042296421 752478270258 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_110132100 ck_110132101 ck_110132102 ck_110132103

theorem ck_110132110 : check target 7 41231686041 42949672959 752478270258 754196257176 = true := by
  decide +kernel

theorem ck_110132111 : check target 7 41231686041 42949672959 754196257176 755914244095 = true := by
  decide +kernel

theorem ck_1101321120 : check target 6 42949672959 43808666418 752478270258 753337263717 = true := by
  decide +kernel

theorem ck_1101321121 : check target 6 42949672959 43808666418 753337263717 754196257176 = true := by
  decide +kernel

theorem ck_1101321122 : check target 6 43808666418 44667659877 752478270258 753337263717 = true := by
  decide +kernel

theorem ck_1101321123 : check target 6 43808666418 44667659877 753337263717 754196257176 = true := by
  decide +kernel

theorem ck_110132112 : check target 7 42949672959 44667659877 752478270258 754196257176 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_1101321120 ck_1101321121 ck_1101321122 ck_1101321123

theorem ck_110132113 : check target 7 42949672959 44667659877 754196257176 755914244095 = true := by
  decide +kernel

theorem ck_11013211 : check target 8 41231686041 44667659877 752478270258 755914244095 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_110132110 ck_110132111 ck_110132112 ck_110132113

theorem ck_11013212 : check target 8 44667659877 48103633714 749042296421 752478270258 = true := by
  decide +kernel

theorem ck_11013213 : check target 8 44667659877 48103633714 752478270258 755914244095 = true := by
  decide +kernel

theorem ck_1101321 : check target 9 41231686041 48103633714 749042296421 755914244095 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_11013210 ck_11013211 ck_11013212 ck_11013213

theorem ck_1101322 : check target 9 48103633714 54975581388 742170348748 749042296421 = true := by
  decide +kernel

theorem ck_1101323 : check target 9 48103633714 54975581388 749042296421 755914244095 = true := by
  decide +kernel

theorem ck_110132 : check target 10 41231686041 54975581388 742170348748 755914244095 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_1101320 ck_1101321 ck_1101322 ck_1101323

theorem ck_110133000 : check target 7 41231686041 42949672959 755914244095 757632231013 = true := by
  decide +kernel

theorem ck_110133001 : check target 7 41231686041 42949672959 757632231013 759350217932 = true := by
  decide +kernel

theorem ck_110133002 : check target 7 42949672959 44667659877 755914244095 757632231013 = true := by
  decide +kernel

theorem ck_110133003 : check target 7 42949672959 44667659877 757632231013 759350217932 = true := by
  decide +kernel

theorem ck_11013300 : check target 8 41231686041 44667659877 755914244095 759350217932 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_110133000 ck_110133001 ck_110133002 ck_110133003

theorem ck_11013301 : check target 8 41231686041 44667659877 759350217932 762786191769 = true := by
  decide +kernel

theorem ck_11013302 : check target 8 44667659877 48103633714 755914244095 759350217932 = true := by
  decide +kernel

theorem ck_11013303 : check target 8 44667659877 48103633714 759350217932 762786191769 = true := by
  decide +kernel

theorem ck_1101330 : check target 9 41231686041 48103633714 755914244095 762786191769 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_11013300 ck_11013301 ck_11013302 ck_11013303

theorem ck_11013310 : check target 8 41231686041 44667659877 762786191769 766222165606 = true := by
  decide +kernel

theorem ck_11013311 : check target 8 41231686041 44667659877 766222165606 769658139443 = true := by
  decide +kernel

theorem ck_11013312 : check target 8 44667659877 48103633714 762786191769 766222165606 = true := by
  decide +kernel

theorem ck_11013313 : check target 8 44667659877 48103633714 766222165606 769658139443 = true := by
  decide +kernel

theorem ck_1101331 : check target 9 41231686041 48103633714 762786191769 769658139443 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_11013310 ck_11013311 ck_11013312 ck_11013313

theorem ck_1101332 : check target 9 48103633714 54975581388 755914244095 762786191769 = true := by
  decide +kernel

theorem ck_1101333 : check target 9 48103633714 54975581388 762786191769 769658139443 = true := by
  decide +kernel

theorem ck_110133 : check target 10 41231686041 54975581388 755914244095 769658139443 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_1101330 ck_1101331 ck_1101332 ck_1101333

theorem ck_11013 : check target 11 27487790694 54975581388 742170348748 769658139443 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_110130 ck_110131 ck_110132 ck_110133

theorem ck_1101 : check target 12 0 54975581388 714682558054 769658139443 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_11010 ck_11011 ck_11012 ck_11013

theorem ck_1102 : check target 12 54975581388 109951162777 659706976665 714682558054 = true := by
  decide +kernel

theorem ck_1103 : check target 12 54975581388 109951162777 714682558054 769658139443 = true := by
  decide +kernel

theorem ck_110 : check target 13 0 109951162777 659706976665 769658139443 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_1100 ck_1101 ck_1102 ck_1103

theorem ck_11100 : check target 11 0 27487790694 769658139443 797145930137 = true := by
  decide +kernel

theorem ck_11101 : check target 11 0 27487790694 797145930137 824633720832 = true := by
  decide +kernel

theorem ck_111020 : check target 10 27487790694 41231686041 769658139443 783402034790 = true := by
  decide +kernel

theorem ck_111021 : check target 10 27487790694 41231686041 783402034790 797145930137 = true := by
  decide +kernel

theorem ck_1110220 : check target 9 41231686041 48103633714 769658139443 776530087116 = true := by
  decide +kernel

theorem ck_1110221 : check target 9 41231686041 48103633714 776530087116 783402034790 = true := by
  decide +kernel

theorem ck_1110222 : check target 9 48103633714 54975581388 769658139443 776530087116 = true := by
  decide +kernel

theorem ck_1110223 : check target 9 48103633714 54975581388 776530087116 783402034790 = true := by
  decide +kernel

theorem ck_111022 : check target 10 41231686041 54975581388 769658139443 783402034790 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_1110220 ck_1110221 ck_1110222 ck_1110223

theorem ck_1110230 : check target 9 41231686041 48103633714 783402034790 790273982463 = true := by
  decide +kernel

theorem ck_1110231 : check target 9 41231686041 48103633714 790273982463 797145930137 = true := by
  decide +kernel

theorem ck_1110232 : check target 9 48103633714 54975581388 783402034790 790273982463 = true := by
  decide +kernel

theorem ck_1110233 : check target 9 48103633714 54975581388 790273982463 797145930137 = true := by
  decide +kernel

theorem ck_111023 : check target 10 41231686041 54975581388 783402034790 797145930137 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_1110230 ck_1110231 ck_1110232 ck_1110233

theorem ck_11102 : check target 11 27487790694 54975581388 769658139443 797145930137 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_111020 ck_111021 ck_111022 ck_111023

theorem ck_111030 : check target 10 27487790694 41231686041 797145930137 810889825484 = true := by
  decide +kernel

theorem ck_111031 : check target 10 27487790694 41231686041 810889825484 824633720832 = true := by
  decide +kernel

theorem ck_111032 : check target 10 41231686041 54975581388 797145930137 810889825484 = true := by
  decide +kernel

theorem ck_111033 : check target 10 41231686041 54975581388 810889825484 824633720832 = true := by
  decide +kernel

theorem ck_11103 : check target 11 27487790694 54975581388 797145930137 824633720832 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_111030 ck_111031 ck_111032 ck_111033

theorem ck_1110 : check target 12 0 54975581388 769658139443 824633720832 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_11100 ck_11101 ck_11102 ck_11103

theorem ck_11110 : check target 11 0 27487790694 824633720832 852121511526 = true := by
  decide +kernel

theorem ck_11111 : check target 11 0 27487790694 852121511526 879609302221 = true := by
  decide +kernel

theorem ck_111120 : check target 10 27487790694 41231686041 824633720832 838377616179 = true := by
  decide +kernel

theorem ck_111121 : check target 10 27487790694 41231686041 838377616179 852121511526 = true := by
  decide +kernel

theorem ck_111122 : check target 10 41231686041 54975581388 824633720832 838377616179 = true := by
  decide +kernel

theorem ck_111123 : check target 10 41231686041 54975581388 838377616179 852121511526 = true := by
  decide +kernel

theorem ck_11112 : check target 11 27487790694 54975581388 824633720832 852121511526 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_111120 ck_111121 ck_111122 ck_111123

theorem ck_11113 : check target 11 27487790694 54975581388 852121511526 879609302221 = true := by
  decide +kernel

theorem ck_1111 : check target 12 0 54975581388 824633720832 879609302221 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_11110 ck_11111 ck_11112 ck_11113

theorem ck_1112 : check target 12 54975581388 109951162777 769658139443 824633720832 = true := by
  decide +kernel

theorem ck_1113 : check target 12 54975581388 109951162777 824633720832 879609302221 = true := by
  decide +kernel

theorem ck_111 : check target 13 0 109951162777 769658139443 879609302221 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_1110 ck_1111 ck_1112 ck_1113

theorem ck_112 : check target 13 109951162777 219902325555 659706976665 769658139443 = true := by
  decide +kernel

theorem ck_113 : check target 13 109951162777 219902325555 769658139443 879609302221 = true := by
  decide +kernel

theorem ck_11 : check target 14 0 219902325555 659706976665 879609302221 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_110 ck_111 ck_112 ck_113

theorem ck_12 : check target 14 219902325555 439804651110 439804651110 659706976665 = true := by
  decide +kernel

theorem ck_13 : check target 14 219902325555 439804651110 659706976665 879609302221 = true := by
  decide +kernel

theorem ck_1 : check target 15 0 439804651110 439804651110 879609302221 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_10 ck_11 ck_12 ck_13

theorem ck_2 : check target 15 439804651110 879609302221 0 439804651110 = true := by
  decide +kernel

theorem ck_3 : check target 15 439804651110 879609302221 439804651110 879609302221 = true := by
  decide +kernel

theorem ck_ : check target 16 0 879609302221 0 879609302221 = true :=
  check_succ_of (by norm_num) (by norm_num) ck_0 ck_1 ck_2 ck_3

/-- **The computation**: every box of `[0, 0.8]²` is discarded (4481 boxes in all). -/
theorem check_top : check target 16 0 top 0 top = true := ck_

/-! ## Localization -/

/-- **Localization of Gerver's constants**: for every solution of Romik's system, `(φ, θ)` lies in
the target box. -/
theorem Spec_mem_target {A B φ θ : ℝ} (h : Spec A B φ θ) :
    target.1.Mem φ ∧ target.2.Mem θ := by
  obtain ⟨hQ, hR⟩ := QE_RE_eq_zero h
  obtain ⟨hφ0, hφθ, hθ, -⟩ := h
  have hpi := Real.pi_lt_d2
  have htop := top_ge
  have hS := S_pos
  refine check_sound target 16 0 top 0 top check_top ⟨?_, ?_⟩ ⟨?_, ?_⟩ hφθ hQ hR
  · simp only [Int.cast_zero, zero_div]; exact hφ0
  · linarith
  · simp only [Int.cast_zero, zero_div]; linarith
  · linarith

end Sofa.GC
