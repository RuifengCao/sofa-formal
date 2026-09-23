/-
# Sofa/GerverConn.lean — Gerver's sofa is connected; the upstream `isMovingSofa_gerversSofa`

`gerversSofa = H₀ ∩ H₁ ∩ ⋂_{α ∈ [0, π/2]} L_α` (upstream).  In the hallway frame at angle `α` a
point `z` has coordinates `ca α z = ⟪z, u α⟫ − p₁ α`, `cb α z = ⟪z, v α⟫ − p₂ α`; `z ∈ L_α` iff
`ca, cb ≤ 1` (outer walls) and not `ca < 0 ∧ cb < 0` (inner quadrant).  So
`gerversSofa = Cvx ∩ {no inner quadrant}` with `Cvx` convex (`mem_gerversSofa_iff`), and moving a
point upwards never enters an inner quadrant (`up_mem`).

**Connectedness** (`isConnected_gerversSofa`) follows from four facts about Gerver's path:

* (Q1) `p₁ α sin α + p₂ α cos α < 9/10`: the inner corners stay below height `9/10`, so the part
  `Cvx ∩ {y ≥ 9/10}` lies in the sofa;
* (Q2) `p₂ α ≤ (8/5) sin α` and `p₁ α ≤ (7/20) cos α`: no inner quadrant reaches the regions
  `x ≤ −8/5` and `x ≥ 7/20`, so `Cvx` restricted to them lies in the sofa;
* (Q3) `(−8/5, 9/10)` and `(7/20, 9/10)` lie in `Cvx`.

Then every point of the sofa is joined to the convex set `Cvx ∩ {y ≥ 9/10}` by a vertical segment
or through one of the two convex end pieces.  (Q1)–(Q3) are certified by interval arithmetic on the
closed forms of `p` (`Sofa/GerverClosed.lean`) over `α ∈ [0, π/2]`, except near `α = 0` and
`α = π/2` where (Q2) is tight and is proved analytically.

Hence **Gerver's sofa is a moving sofa** (`isMovingSofa_gerversSofa'`; the upstream statement
`isMovingSofa_gerversSofa` is still a `sorry` in the upstream file, which cannot import this file).

STATUS: [PROOF-C-local] round 38 (2026-09-23, Opus 5.5).
-/
import Sofa.GerverClosed

noncomputable section

open Real Set MeasureTheory intervalIntegral MovingSofa
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

/- The kernel checks below run one after the other (see `Sofa/GerverConst.lean`). -/
set_option Elab.async false

namespace Sofa.GP

open GC IA
open MovingSofa.GerversSofa (A B φ θ r)

/-! ## Interval sine and cosine on `[0, 2]` -/

/-- `⌊1.57 · 2⁴⁰⌋`, below `π/2`. -/
def q157 : ℤ := qdn (157 / 100)

/-- Enclosure of `sin` on an interval inside `[0, 2]`: `sin` is concave on `[0, π]` (the minimum
is at an end point) and increasing on `[0, π/2]`. -/
def sinW (a : Iv) : Iv :=
  if 0 ≤ a.lo ∧ a.hi ≤ 2 * S then
    ⟨min (sinLB a.lo) (sinLB a.hi), if a.hi ≤ q157 then sinUB a.hi else S⟩
  else ⟨-S, S⟩

/-- Enclosure of `cos` on an interval inside `[0, 2]` (`cos` is decreasing on `[0, π]`). -/
def cosW (a : Iv) : Iv :=
  if 0 ≤ a.lo ∧ a.hi ≤ 2 * S then ⟨cosLB a.hi, cosUB a.lo⟩ else ⟨-S, S⟩

lemma mem_sinW {x : ℝ} {a : Iv} (hx : a.Mem x) : (sinW a).Mem (Real.sin x) := by
  have hS := S_pos
  have hpi := Real.pi_gt_d2
  unfold sinW
  by_cases h : 0 ≤ a.lo ∧ a.hi ≤ 2 * S
  · rw [if_pos h]
    obtain ⟨h0, h1⟩ := h
    have hlo : (0 : ℝ) ≤ (a.lo : ℝ) / S := div_nonneg (by exact_mod_cast h0) hS.le
    have hhi : (a.hi : ℝ) / S ≤ 2 := by rw [div_le_iff₀ hS]; exact_mod_cast h1
    have hxhi : 0 ≤ (a.hi : ℝ) / S := hlo.trans (hx.1.trans hx.2)
    refine ⟨?_, ?_⟩
    · have hm := strictConcaveOn_sin_Icc.concaveOn.min_le_of_mem_Icc
        (x := (a.lo : ℝ) / S) (y := (a.hi : ℝ) / S) (z := x)
        ⟨hlo, by linarith [hx.1, hx.2]⟩ ⟨hxhi, by linarith⟩ ⟨hx.1, hx.2⟩
      refine le_trans ?_ hm
      show (((min (sinLB a.lo) (sinLB a.hi) : ℤ) : ℝ)) / S ≤ _
      push_cast
      rw [← min_div_div_right hS.le]
      exact min_le_min (sinLB_le hlo) (sinLB_le hxhi)
    · show Real.sin x ≤ (((if a.hi ≤ q157 then sinUB a.hi else S : ℤ)) : ℝ) / S
      split_ifs with h'
      · have hq : (q157 : ℝ) / S ≤ 157 / 100 := by
          have := qdn_le (157 / 100 : ℚ); push_cast at this; exact this
        have hh : (a.hi : ℝ) / S ≤ 157 / 100 :=
          (div_le_div_of_nonneg_right (by exact_mod_cast h') hS.le).trans hq
        exact (Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hx.1]) (by linarith)
          hx.2).trans (le_sinUB hxhi)
      · rw [div_self hS.ne']; exact Real.sin_le_one x
  · rw [if_neg h]
    refine ⟨?_, ?_⟩
    · show ((-S : ℤ) : ℝ) / S ≤ _
      rw [Int.cast_neg, neg_div, div_self hS.ne']; exact Real.neg_one_le_sin x
    · show _ ≤ ((S : ℤ) : ℝ) / S
      rw [div_self hS.ne']; exact Real.sin_le_one x

lemma mem_cosW {x : ℝ} {a : Iv} (hx : a.Mem x) : (cosW a).Mem (Real.cos x) := by
  have hS := S_pos
  have hpi := Real.pi_gt_d2
  unfold cosW
  split_ifs with h
  · obtain ⟨h0, h1⟩ := h
    have hlo : (0 : ℝ) ≤ (a.lo : ℝ) / S := div_nonneg (by exact_mod_cast h0) hS.le
    have hhi : (a.hi : ℝ) / S ≤ 2 := by
      rw [div_le_iff₀ hS]; exact_mod_cast h1
    refine ⟨?_, ?_⟩
    · exact (cosLB_le (hlo.trans (hx.1.trans hx.2))).trans
        (Real.cos_le_cos_of_nonneg_of_le_pi (hlo.trans hx.1) (by linarith) hx.2)
    · exact (Real.cos_le_cos_of_nonneg_of_le_pi hlo (by linarith [hx.2]) hx.1).trans
        (le_cosUB hlo)
  · refine ⟨?_, ?_⟩
    · rw [Int.cast_neg, neg_div, div_self hS.ne']; exact Real.neg_one_le_cos x
    · rw [div_self hS.ne']; exact Real.cos_le_one x

/-! ## The variables along the path -/

/-- Variables: `0 ↦ α`, `1 ↦ sin α`, `2 ↦ cos α`, `3 ↦ φ`, `4 ↦ θ`, `5 ↦ π`, `6 ↦ sin φ`,
`7 ↦ cos φ`, `8 ↦ sin θ`, `9 ↦ cos θ`, `10 ↦ A`, `11 ↦ B`. -/
def envA (α : ℝ) : ℕ → ℝ
  | 0 => α
  | 1 => Real.sin α
  | 2 => Real.cos α
  | 3 => φ
  | 4 => θ
  | 5 => π
  | 6 => Real.sin φ
  | 7 => Real.cos φ
  | 8 => Real.sin θ
  | 9 => Real.cos θ
  | 10 => A
  | 11 => B
  | _ => 0

/-- The interval values of the variables for `α ∈ [lo, hi] · 2⁻⁴⁰`. -/
def boxA (lo hi : ℤ) : ℕ → Iv
  | 0 => ⟨lo, hi⟩
  | 1 => sinW ⟨lo, hi⟩
  | 2 => cosW ⟨lo, hi⟩
  | 3 => tbox.1
  | 4 => tbox.2
  | 5 => piIv
  | 6 => Iv.sin tbox.1
  | 7 => Iv.cos tbox.1
  | 8 => Iv.sin tbox.2
  | 9 => Iv.cos tbox.2
  | 10 => ⟨aLo, aHi⟩
  | 11 => ⟨bLo, bHi⟩
  | _ => ⟨0, 0⟩

lemma mem_boxA {α : ℝ} {lo hi : ℤ} (h : Iv.Mem ⟨lo, hi⟩ α) : ∀ i, (boxA lo hi i).Mem (envA α i)
  | 0 => h
  | 1 => mem_sinW h
  | 2 => mem_cosW h
  | 3 => φ_mem
  | 4 => θ_mem
  | 5 => mem_piIv
  | 6 => Iv.mem_sin φ_mem
  | 7 => Iv.mem_cos φ_mem
  | 8 => Iv.mem_sin θ_mem
  | 9 => Iv.mem_cos θ_mem
  | 10 => A_mem
  | 11 => B_mem
  | _ + 12 => by
    show ((0 : ℤ) : ℝ) / S ≤ 0 ∧ (0 : ℝ) ≤ ((0 : ℤ) : ℝ) / S
    simp

/-! ## The closed forms as interval expressions -/

def eα : IE := .v 0
def esα : IE := .v 1
def ecα : IE := .v 2
def eφ : IE := .v 3
def eθ : IE := .v 4
def eπ : IE := .v 5
def esφ : IE := .v 6
def ecφ : IE := .v 7
def esθ : IE := .v 8
def ecθ : IE := .v 9
def eA : IE := .v 10
def eB : IE := .v 11

/-- `Fs` as an expression. -/
def FsE (a b c t s co : IE) : IE :=
  -((a + b * t + c * (t * t)) * co) + (b + k 2 * c * t) * s + k 2 * c * co

/-- `Fc` as an expression. -/
def FcE (a b c t s co : IE) : IE :=
  (a + b * t + c * (t * t)) * s + (b + k 2 * c * t) * co - k 2 * c * s

lemma FsE_eval (env : ℕ → ℝ) (a b c t s co : IE) : (FsE a b c t s co).eval env =
    Fs (a.eval env) (b.eval env) (c.eval env) (t.eval env) (s.eval env) (co.eval env) := by
  simp only [FsE, Fs, k, IE.eval_add', IE.eval_mul', IE.eval_neg', IE.eval_c]
  push_cast; ring

lemma FcE_eval (env : ℕ → ℝ) (a b c t s co : IE) : (FcE a b c t s co).eval env =
    Fc (a.eval env) (b.eval env) (c.eval env) (t.eval env) (s.eval env) (co.eval env) := by
  simp only [FcE, Fc, k, IE.eval_add', IE.eval_sub', IE.eval_mul', IE.eval_c]
  push_cast; ring

/-- `π/2 − φ` and `π/2 − θ`. -/
def eHφ : IE := eπ * k (1 / 2) - eφ
def eHθ : IE := eπ * k (1 / 2) - eθ

def raE : ℕ → IE
  | 0 => k (1 / 2)
  | 1 => (k 1 + eA - eφ) * k (1 / 2)
  | 2 => eA - eφ
  | _ => eB - eHφ * (k 1 + eA) * k (1 / 2) - eHφ * eHφ * k (1 / 4)

def rbE : ℕ → IE
  | 0 => k 0
  | 1 => k (1 / 2)
  | 2 => k 1
  | _ => (k 1 + eA) * k (1 / 2) + eHφ * k (1 / 2)

def rcE : ℕ → IE
  | 0 => k 0
  | 1 => k 0
  | 2 => k 0
  | _ => k (-1 / 4)

/-- The break points, their sines and cosines. -/
def brkE : ℕ → IE
  | 0 => k 0
  | 1 => eφ
  | 2 => eθ
  | 3 => eHθ
  | _ => eHφ

def sbrkE : ℕ → IE
  | 0 => k 0
  | 1 => esφ
  | 2 => esθ
  | 3 => ecθ
  | _ => ecφ

def cbrkE : ℕ → IE
  | 0 => k 1
  | 1 => ecφ
  | 2 => ecθ
  | 3 => esθ
  | _ => esφ

lemma raE_eval (α : ℝ) (j : ℕ) (hj : j ≤ 3) : (raE j).eval (envA α) = ra j := by
  interval_cases j <;>
    simp only [raE, ra, eHφ, eA, eB, eφ, eπ, k, IE.eval_add', IE.eval_sub', IE.eval_mul',
      IE.eval_v, IE.eval_c, envA] <;> push_cast <;> ring

lemma rbE_eval (α : ℝ) (j : ℕ) (hj : j ≤ 3) : (rbE j).eval (envA α) = rb j := by
  interval_cases j <;>
    simp only [rbE, rb, eHφ, eA, eφ, eπ, k, IE.eval_add', IE.eval_sub', IE.eval_mul',
      IE.eval_v, IE.eval_c, envA] <;> push_cast <;> ring

lemma rcE_eval (α : ℝ) (j : ℕ) (hj : j ≤ 3) : (rcE j).eval (envA α) = rc j := by
  interval_cases j <;> simp only [rcE, rc, k, IE.eval_c] <;> push_cast <;> ring

lemma brkE_eval (α : ℝ) (j : ℕ) (hj : j ≤ 4) :
    (brkE j).eval (envA α) = brk j ∧ (sbrkE j).eval (envA α) = Real.sin (brk j) ∧
      (cbrkE j).eval (envA α) = Real.cos (brk j) := by
  interval_cases j
  · refine ⟨?_, ?_, ?_⟩ <;> simp [brkE, sbrkE, cbrkE, brk, k]
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp only [brkE, brk, eHθ, eπ, eθ, k, IE.eval_sub', IE.eval_mul', IE.eval_v, IE.eval_c,
        envA]
      push_cast; ring
    · simp only [sbrkE, brk, ecθ, IE.eval_v, envA, sin_pi_div_two_sub]
    · simp only [cbrkE, brk, esθ, IE.eval_v, envA, cos_pi_div_two_sub]
  · refine ⟨?_, ?_, ?_⟩
    · simp only [brkE, brk, eHφ, eπ, eφ, k, IE.eval_sub', IE.eval_mul', IE.eval_v, IE.eval_c,
        envA]
      push_cast; ring
    · simp only [sbrkE, brk, ecφ, IE.eval_v, envA, sin_pi_div_two_sub]
    · simp only [cbrkE, brk, esφ, IE.eval_v, envA, cos_pi_div_two_sub]

/-- `∫` over the whole piece, as an expression. -/
def SYE (j : ℕ) : IE :=
  FsE (raE j) (rbE j) (rcE j) (brkE (j + 1)) (sbrkE (j + 1)) (cbrkE (j + 1))
    - FsE (raE j) (rbE j) (rcE j) (brkE j) (sbrkE j) (cbrkE j)

def SXE (j : ℕ) : IE :=
  FcE (raE j) (rbE j) (rcE j) (brkE (j + 1)) (sbrkE (j + 1)) (cbrkE (j + 1))
    - FcE (raE j) (rbE j) (rcE j) (brkE j) (sbrkE j) (cbrkE j)

lemma SYE_eval (α : ℝ) (j : ℕ) (hj : j ≤ 3) : (SYE j).eval (envA α) = SY j := by
  obtain ⟨b1, b2, b3⟩ := brkE_eval α (j + 1) (by omega)
  obtain ⟨c1, c2, c3⟩ := brkE_eval α j (by omega)
  simp only [SYE, SY, IE.eval_sub', FsE_eval, raE_eval α j hj, rbE_eval α j hj, rcE_eval α j hj,
    b1, b2, b3, c1, c2, c3]

lemma SXE_eval (α : ℝ) (j : ℕ) (hj : j ≤ 3) : (SXE j).eval (envA α) = SX j := by
  obtain ⟨b1, b2, b3⟩ := brkE_eval α (j + 1) (by omega)
  obtain ⟨c1, c2, c3⟩ := brkE_eval α j (by omega)
  simp only [SXE, SX, IE.eval_sub', FcE_eval, raE_eval α j hj, rbE_eval α j hj, rcE_eval α j hj,
    b1, b2, b3, c1, c2, c3]

def tailYE : ℕ → IE
  | 0 => SYE 0 + SYE 1 + SYE 2 + SYE 3
  | 1 => SYE 1 + SYE 2 + SYE 3
  | 2 => SYE 2 + SYE 3
  | 3 => SYE 3
  | _ => k 0

def tailXE : ℕ → IE
  | 0 => SXE 0 + SXE 1 + SXE 2 + SXE 3
  | 1 => SXE 1 + SXE 2 + SXE 3
  | 2 => SXE 2 + SXE 3
  | 3 => SXE 3
  | _ => k 0

lemma tailYE_eval (α : ℝ) (j : ℕ) (hj : j ≤ 4) : (tailYE j).eval (envA α) = tailY j := by
  interval_cases j <;> simp [tailYE, tailY, SYE_eval, k]

lemma tailXE_eval (α : ℝ) (j : ℕ) (hj : j ≤ 4) : (tailXE j).eval (envA α) = tailX j := by
  interval_cases j <;> simp [tailXE, tailX, SXE_eval, k]

/-- `yC` and `xC` as expressions. -/
def yCE (j : ℕ) (t s co : IE) : IE :=
  FsE (raE j) (rbE j) (rcE j) (brkE (j + 1)) (sbrkE (j + 1)) (cbrkE (j + 1))
    - FsE (raE j) (rbE j) (rcE j) t s co + tailYE (j + 1)

def xCE (j : ℕ) (t s co : IE) : IE :=
  k 1 - (FcE (raE j) (rbE j) (rcE j) (brkE (j + 1)) (sbrkE (j + 1)) (cbrkE (j + 1))
    - FcE (raE j) (rbE j) (rcE j) t s co + tailXE (j + 1))

lemma yCE_eval (α : ℝ) (j : ℕ) (hj : j ≤ 3) (t s co : IE) : (yCE j t s co).eval (envA α) =
    yC j (t.eval (envA α)) (s.eval (envA α)) (co.eval (envA α)) := by
  obtain ⟨b1, b2, b3⟩ := brkE_eval α (j + 1) (by omega)
  simp only [yCE, yC, IE.eval_sub', IE.eval_add', FsE_eval, raE_eval α j hj, rbE_eval α j hj,
    rcE_eval α j hj, b1, b2, b3, tailYE_eval α (j + 1) (by omega)]

lemma xCE_eval (α : ℝ) (j : ℕ) (hj : j ≤ 3) (t s co : IE) : (xCE j t s co).eval (envA α) =
    xC j (t.eval (envA α)) (s.eval (envA α)) (co.eval (envA α)) := by
  obtain ⟨b1, b2, b3⟩ := brkE_eval α (j + 1) (by omega)
  simp only [xCE, xC, k, IE.eval_sub', IE.eval_add', IE.eval_c, FcE_eval, raE_eval α j hj,
    rbE_eval α j hj, rcE_eval α j hj, b1, b2, b3, tailXE_eval α (j + 1) (by omega),
    Rat.cast_one]

/-- `x 0` as an expression. -/
def x0E : IE := xCE 0 (k 0) (k 0) (k 1)

lemma x0E_eval (α : ℝ) : x0E.eval (envA α) = x0C := by
  rw [x0E, xCE_eval α 0 (by norm_num)]
  simp [k, x0C]

/-- `π/2 − α` with its sine and cosine. -/
def eβ : IE := eπ * k (1 / 2) - eα

lemma eβ_eval (α : ℝ) : eβ.eval (envA α) = π / 2 - α := by
  simp only [eβ, eπ, eα, k, IE.eval_sub', IE.eval_mul', IE.eval_v, IE.eval_c, envA]
  push_cast; ring

/-- `p₁C` and `p₂C` as expressions. -/
def p1E : ℕ → IE
  | 0 => ecα - k 1
  | 1 => xCE 3 eβ ecα esα * ecα + yCE 3 eβ ecα esα * esα - k 1
  | 2 => xCE 2 eβ ecα esα * ecα + yCE 2 eβ ecα esα * esα - k 1
  | 3 => xCE 1 eβ ecα esα * ecα + yCE 1 eβ ecα esα * esα - k 1
  | _ => xCE 0 eβ ecα esα * ecα + yCE 0 eβ ecα esα * esα - k 1

def p2E : ℕ → IE
  | 0 => yCE 0 eα esα ecα * ecα - (k 4 * x0E - k 2 - xCE 0 eα esα ecα) * esα - k 1
  | 1 => yCE 1 eα esα ecα * ecα - (k 4 * x0E - k 2 - xCE 1 eα esα ecα) * esα - k 1
  | 2 => yCE 2 eα esα ecα * ecα - (k 4 * x0E - k 2 - xCE 2 eα esα ecα) * esα - k 1
  | 3 => yCE 3 eα esα ecα * ecα - (k 4 * x0E - k 2 - xCE 3 eα esα ecα) * esα - k 1
  | _ => -((k 4 * x0E - k 3) * esα) - k 1

lemma p1E_eval (α : ℝ) (j : ℕ) (hj : j ≤ 4) : (p1E j).eval (envA α) = p₁C j α := by
  have hs : esα.eval (envA α) = Real.sin α := rfl
  have hc : ecα.eval (envA α) = Real.cos α := rfl
  interval_cases j <;>
    simp only [p1E, p₁C, IE.eval_sub', IE.eval_add', IE.eval_mul', k, IE.eval_c, Rat.cast_one,
      hs, hc, eβ_eval, xCE_eval α _ (by norm_num : (3 : ℕ) ≤ 3),
      xCE_eval α _ (by norm_num : (2 : ℕ) ≤ 3), xCE_eval α _ (by norm_num : (1 : ℕ) ≤ 3),
      xCE_eval α _ (by norm_num : (0 : ℕ) ≤ 3), yCE_eval α _ (by norm_num : (3 : ℕ) ≤ 3),
      yCE_eval α _ (by norm_num : (2 : ℕ) ≤ 3), yCE_eval α _ (by norm_num : (1 : ℕ) ≤ 3),
      yCE_eval α _ (by norm_num : (0 : ℕ) ≤ 3)]

lemma p2E_eval (α : ℝ) (j : ℕ) (hj : j ≤ 4) : (p2E j).eval (envA α) = p₂C j α := by
  have hs : esα.eval (envA α) = Real.sin α := rfl
  have hc : ecα.eval (envA α) = Real.cos α := rfl
  have ha : eα.eval (envA α) = α := rfl
  interval_cases j <;>
    simp only [p2E, p₂C, IE.eval_sub', IE.eval_mul', IE.eval_neg', k, IE.eval_c, neg_mul,
      Rat.cast_one, Rat.cast_ofNat, hs, hc, ha, x0E_eval,
      xCE_eval α _ (by norm_num : (3 : ℕ) ≤ 3),
      xCE_eval α _ (by norm_num : (2 : ℕ) ≤ 3), xCE_eval α _ (by norm_num : (1 : ℕ) ≤ 3),
      xCE_eval α _ (by norm_num : (0 : ℕ) ≤ 3), yCE_eval α _ (by norm_num : (3 : ℕ) ≤ 3),
      yCE_eval α _ (by norm_num : (2 : ℕ) ≤ 3), yCE_eval α _ (by norm_num : (1 : ℕ) ≤ 3),
      yCE_eval α _ (by norm_num : (0 : ℕ) ≤ 3)]

/-! ## The interval check along `[0, π/2]` -/

/-- Integer bounds of the break points: `brkLo j / S ≤ brk j ≤ brkHi j / S`. -/
def brkLo : ℕ → ℤ
  | 0 => 0
  | 1 => tbox.1.lo
  | 2 => tbox.2.lo
  | 3 => piIv.lo / 2 - tbox.2.hi
  | 4 => piIv.lo / 2 - tbox.1.hi
  | _ => piIv.lo / 2

def brkHi : ℕ → ℤ
  | 0 => 0
  | 1 => tbox.1.hi
  | 2 => tbox.2.hi
  | 3 => -((-piIv.hi) / 2) - tbox.2.lo
  | 4 => -((-piIv.hi) / 2) - tbox.1.lo
  | _ => -((-piIv.hi) / 2)

lemma half_pi_lo : ((piIv.lo / 2 : ℤ) : ℝ) / S ≤ π / 2 := by
  have hS := S_pos
  have h1 : (piIv.lo / 2) * 2 ≤ piIv.lo := Int.ediv_mul_le _ (by norm_num)
  have h2 : ((piIv.lo / 2 : ℤ) : ℝ) * 2 ≤ piIv.lo := by exact_mod_cast h1
  have h3 := mem_piIv.1
  rw [div_le_iff₀ hS] at h3 ⊢
  nlinarith

lemma half_pi_hi : π / 2 ≤ ((-((-piIv.hi) / 2) : ℤ) : ℝ) / S := by
  have hS := S_pos
  have h1 : ((-piIv.hi) / 2) * 2 ≤ -piIv.hi := Int.ediv_mul_le _ (by norm_num)
  have h2 : (piIv.hi : ℝ) ≤ ((-((-piIv.hi) / 2) : ℤ) : ℝ) * 2 := by
    have : piIv.hi ≤ (-((-piIv.hi) / 2)) * 2 := by linarith
    exact_mod_cast this
  have h3 := mem_piIv.2
  rw [le_div_iff₀ hS] at h3 ⊢
  nlinarith

lemma brk_bounds (j : ℕ) (hj : j ≤ 5) :
    (brkLo j : ℝ) / S ≤ brk j ∧ brk j ≤ (brkHi j : ℝ) / S := by
  have hS := S_pos
  obtain ⟨p1, p2⟩ := φ_mem
  obtain ⟨t1, t2⟩ := θ_mem
  have hl := half_pi_lo
  have hh := half_pi_hi
  interval_cases j
  · simp [brkLo, brkHi, brk]
  · exact ⟨p1, p2⟩
  · exact ⟨t1, t2⟩
  · simp only [brkLo, brkHi, brk, Int.cast_sub, sub_div]
    constructor <;> linarith
  · simp only [brkLo, brkHi, brk, Int.cast_sub, sub_div]
    constructor <;> linarith
  · exact ⟨hl, hh⟩

/-- A box is fine for `F` if, for every piece it may meet, the enclosure of `F` on it is `< 0`. -/
def pieceOK (F : ℕ → IE) (lo hi : ℤ) : Bool :=
  (List.range 5).all fun j => decide (hi < brkLo j) || decide (brkHi (j + 1) < lo)
    || decide (((F j).ieval (boxA lo hi)).hi < 0)

lemma pieceOK_sound {F : ℕ → IE} {lo hi : ℤ} (h : pieceOK F lo hi = true) {α : ℝ}
    (hα : Iv.Mem ⟨lo, hi⟩ α) {j : ℕ} (hj : j < 5) (hαj : α ∈ Icc (brk j) (brk (j + 1))) :
    (F j).eval (envA α) < 0 := by
  have hS := S_pos
  unfold pieceOK at h
  have hj' := List.all_eq_true.1 h j (List.mem_range.2 hj)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hj'
  obtain ⟨b1, -⟩ := brk_bounds j (by omega)
  obtain ⟨-, b2⟩ := brk_bounds (j + 1) (by omega)
  rcases hj' with (h1 | h2) | h3
  · exfalso
    have : (hi : ℝ) / S < (brkLo j : ℝ) / S := div_lt_div_of_pos_right (by exact_mod_cast h1) hS
    linarith [hα.2, hαj.1]
  · exfalso
    have : (brkHi (j + 1) : ℝ) / S < (lo : ℝ) / S :=
      div_lt_div_of_pos_right (by exact_mod_cast h2) hS
    linarith [hα.1, hαj.2]
  · have hm := IE.mem_ieval (mem_boxA hα) (F j)
    have : (((F j).ieval (boxA lo hi)).hi : ℝ) / S < 0 :=
      div_neg_of_neg_of_pos (by exact_mod_cast h3) hS
    exact hm.2.trans_lt this

/-- Bisection along `α`. -/
def chkA (F : ℕ → IE) : ℕ → ℤ → ℤ → Bool
  | 0, lo, hi => pieceOK F lo hi
  | d + 1, lo, hi =>
    pieceOK F lo hi || (chkA F d lo ((lo + hi) / 2) && chkA F d ((lo + hi) / 2) hi)

theorem chkA_sound (F : ℕ → IE) : ∀ (d : ℕ) (lo hi : ℤ), chkA F d lo hi = true → ∀ {α : ℝ},
    Iv.Mem ⟨lo, hi⟩ α → ∀ {j : ℕ}, j < 5 → α ∈ Icc (brk j) (brk (j + 1)) →
      (F j).eval (envA α) < 0
  | 0, _, _, h, _, hα, _, hj, hαj => pieceOK_sound h hα hj hαj
  | d + 1, lo, hi, h, α, hα, j, hj, hαj => by
    unfold chkA at h
    rcases Bool.or_eq_true_iff.1 h with h | h
    · exact pieceOK_sound h hα hj hαj
    simp only [Bool.and_eq_true] at h
    rcases le_total α ((((lo + hi) / 2 : ℤ) : ℝ) / S) with hm | hm
    · exact chkA_sound F d lo _ h.1 ⟨hα.1, hm⟩ hj hαj
    · exact chkA_sound F d _ hi h.2 ⟨hm, hα.2⟩ hj hαj

lemma exists_piece {α : ℝ} (hα : α ∈ Icc 0 (π / 2)) :
    ∃ j < 5, α ∈ Icc (brk j) (brk (j + 1)) := by
  by_cases h1 : α ≤ brk 1
  · exact ⟨0, by norm_num, hα.1, h1⟩
  by_cases h2 : α ≤ brk 2
  · exact ⟨1, by norm_num, (not_le.1 h1).le, h2⟩
  by_cases h3 : α ≤ brk 3
  · exact ⟨2, by norm_num, (not_le.1 h2).le, h3⟩
  by_cases h4 : α ≤ brk 4
  · exact ⟨3, by norm_num, (not_le.1 h3).le, h4⟩
  · exact ⟨4, by norm_num, (not_le.1 h4).le, hα.2⟩

/-- The top of the range `[0, π/2]`. -/
def topA : ℤ := brkHi 5

lemma mem_top {α : ℝ} (hα : α ∈ Icc 0 (π / 2)) : Iv.Mem ⟨0, topA⟩ α :=
  ⟨by simpa using hα.1, hα.2.trans (brk_bounds 5 le_rfl).2⟩

/-- A generic consequence of a check: the closed-form inequality at every `α` of the range. -/
lemma of_chkA {F : ℕ → IE} {d : ℕ} {lo hi : ℤ} (h : chkA F d lo hi = true) {α : ℝ}
    (hα : α ∈ Icc 0 (π / 2)) (hlo : (lo : ℝ) / S ≤ α) (hhi : α ≤ (hi : ℝ) / S) :
    ∃ j < 5, α ∈ Icc (brk j) (brk (j + 1)) ∧ (F j).eval (envA α) < 0 := by
  obtain ⟨j, hj, hαj⟩ := exists_piece hα
  exact ⟨j, hj, hαj, chkA_sound F d lo hi h ⟨hlo, hhi⟩ hj hαj⟩

lemma envA_sin (α : ℝ) : esα.eval (envA α) = Real.sin α := rfl
lemma envA_cos (α : ℝ) : ecα.eval (envA α) = Real.cos α := rfl

/-! ### (Q1): the inner corners stay below height `9/10` -/

def F1E (j : ℕ) : IE := p1E j * esα + p2E j * ecα - k (9 / 10)

theorem ck_F1 : chkA F1E 14 0 topA = true := by
  decide +kernel

theorem Q1 {α : ℝ} (hα : α ∈ Icc 0 (π / 2)) : p₁ α * Real.sin α + p₂ α * Real.cos α < 9 / 10 := by
  obtain ⟨j, hj, hαj, h⟩ := of_chkA ck_F1 hα (by simpa using hα.1) (mem_top hα).2
  simp only [F1E, IE.eval_sub', IE.eval_add', IE.eval_mul', k, IE.eval_c,
    p1E_eval α j (by omega), p2E_eval α j (by omega), envA_sin, envA_cos] at h
  rw [p₁_eq_closed (by omega) hαj, p₂_eq_closed (by omega) hαj]
  push_cast at h
  linarith

/-! ### (Q2): no inner quadrant reaches `x ≤ −8/5` or `x ≥ 7/20` -/

def F2E (j : ℕ) : IE := p2E j - k (8 / 5) * esα

theorem ck_F2 : chkA F2E 14 (qdn (1 / 10)) topA = true := by
  decide +kernel

def F3E (j : ℕ) : IE := p1E j - k (7 / 20) * ecα

theorem ck_F3 : chkA F3E 14 0 (topA - qdn (1 / 10)) = true := by
  decide +kernel

/-- `x 0 ∈ [0.19, 0.2]`. -/
def x0OK : Bool :=
  decide (qup (19 / 100) ≤ (x0E.ieval (boxA 0 0)).lo) && decide ((x0E.ieval (boxA 0 0)).hi ≤ qdn (1 / 5))

theorem x0OK_true : x0OK = true := by
  decide +kernel

lemma x0_bounds : 19 / 100 ≤ GerversSofa.x 0 ∧ GerversSofa.x 0 ≤ 1 / 5 := by
  have hS := S_pos
  have h := x0OK_true
  unfold x0OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hm := IE.mem_ieval (mem_boxA (α := 0) (lo := 0) (hi := 0) ⟨by simp, by simp⟩) x0E
  rw [x0E_eval, ← x_zero_eq] at hm
  constructor
  · have h1 := le_qup (19 / 100 : ℚ)
    have h2 : ((qup (19 / 100) : ℤ) : ℝ) / S ≤ ((x0E.ieval (boxA 0 0)).lo : ℝ) / S :=
      div_le_div_of_nonneg_right (by exact_mod_cast h.1) hS.le
    push_cast at h1
    linarith [hm.1]
  · have h1 := qdn_le (1 / 5 : ℚ)
    have h2 : ((x0E.ieval (boxA 0 0)).hi : ℝ) / S ≤ ((qdn (1 / 5) : ℤ) : ℝ) / S :=
      div_le_div_of_nonneg_right (by exact_mod_cast h.2) hS.le
    push_cast at h1
    linarith [hm.2]

/-- `y ≤ 1` on `[0, π/2 − φ]` (`y 0 = 1`, `y` is decreasing). -/
lemma y_le_one {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ π / 2 - φ) : GerversSofa.y α ≤ 1 := by
  have hpi := Real.pi_gt_d2
  have e : GerversSofa.y 0 = (∫ t in (0 : ℝ)..α, r t * Real.sin t) + GerversSofa.y α := by
    rw [GerversSofa.y, GerversSofa.y, integral_add_adjacent_intervals
      (intervalIntegrable_r_mul continuous_sin _ _) (intervalIntegrable_r_mul continuous_sin _ _)]
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..α, r t * Real.sin t :=
    integral_nonneg h0 fun t ht => mul_nonneg (r_nonneg_le t).1
      (sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, (bounds).1]))
  rw [y_zero] at e
  linarith

/-- `x α ≤ x 0 + (3/2) α` on `[0, π/2 − φ]` (`0 ≤ r ≤ 3/2`). -/
lemma x_le {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ π / 2 - φ) :
    GerversSofa.x α ≤ GerversSofa.x 0 + 3 / 2 * α := by
  have hpi := Real.pi_gt_d2
  have e : GerversSofa.x α = GerversSofa.x 0 + ∫ t in (0 : ℝ)..α, r t * Real.cos t := by
    rw [GerversSofa.x, GerversSofa.x, ← integral_add_adjacent_intervals
      (intervalIntegrable_r_mul continuous_cos 0 α) (intervalIntegrable_r_mul continuous_cos α _)]
    ring
  have hle : ∫ t in (0 : ℝ)..α, r t * Real.cos t ≤ ∫ t in (0 : ℝ)..α, (3 / 2 : ℝ) :=
    integral_mono_on h0 (intervalIntegrable_r_mul continuous_cos _ _) intervalIntegrable_const
      fun t ht => by
        obtain ⟨r0, r1⟩ := r_nonneg_le t
        have hc1 := Real.cos_le_one t
        have hc0 : 0 ≤ Real.cos t := cos_nonneg_of_mem_Icc ⟨by linarith [ht.1],
          by linarith [ht.2, (bounds).1]⟩
        nlinarith
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle
  rw [e]
  linarith

theorem Q2L {α : ℝ} (hα : α ∈ Icc 0 (π / 2)) : p₂ α ≤ 8 / 5 * Real.sin α := by
  obtain ⟨p1, p2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  have hs0 : 0 ≤ Real.sin α := sin_nonneg_of_nonneg_of_le_pi hα.1 (by linarith [hα.2])
  have hc0 : 0 ≤ Real.cos α := cos_nonneg_of_mem_Icc ⟨by linarith [hα.1], hα.2⟩
  by_cases hsmall : α ≤ 1 / 10
  · have hαb : α ≤ π / 2 - φ := by linarith
    rw [p₂, if_pos hαb]
    have hy := y_le_one hα.1 hαb
    have hx := x_le hα.1 hαb
    obtain ⟨x01, -⟩ := x0_bounds
    have hc1 := Real.cos_le_one α
    have h1 : GerversSofa.y α * Real.cos α ≤ 1 := by nlinarith
    have h2 : (GerversSofa.x α - 4 * GerversSofa.x 0 + 2) * Real.sin α ≤ 8 / 5 * Real.sin α :=
      mul_le_mul_of_nonneg_right (by linarith) hs0
    nlinarith
  · obtain ⟨j, hj, hαj, h⟩ := of_chkA ck_F2 hα
      ((qdn_le (1 / 10 : ℚ)).trans (by push_cast; linarith)) (mem_top hα).2
    simp only [F2E, IE.eval_sub', IE.eval_mul', k, IE.eval_c, p2E_eval α j (by omega),
      envA_sin] at h
    rw [p₂_eq_closed (by omega) hαj]
    push_cast at h
    linarith

theorem Q2R {α : ℝ} (hα : α ∈ Icc 0 (π / 2)) : p₁ α ≤ 7 / 20 * Real.cos α := by
  obtain ⟨p1, p2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  have hs0 : 0 ≤ Real.sin α := sin_nonneg_of_nonneg_of_le_pi hα.1 (by linarith [hα.2])
  have hc0 : 0 ≤ Real.cos α := cos_nonneg_of_mem_Icc ⟨by linarith [hα.1], hα.2⟩
  by_cases hbig : π / 2 - 1 / 10 ≤ α
  · have hαφ : ¬ α ≤ φ := by linarith
    rw [p₁, if_neg hαφ]
    have hβ0 : 0 ≤ π / 2 - α := by linarith [hα.2]
    have hβ1 : π / 2 - α ≤ π / 2 - φ := by linarith
    have hy := y_le_one hβ0 hβ1
    have hx := x_le hβ0 hβ1
    obtain ⟨-, x02⟩ := x0_bounds
    have hs1 := Real.sin_le_one α
    have h1 : GerversSofa.y (π / 2 - α) * Real.sin α ≤ 1 := by nlinarith
    have h2 : GerversSofa.x (π / 2 - α) * Real.cos α ≤ 7 / 20 * Real.cos α :=
      mul_le_mul_of_nonneg_right (by linarith) hc0
    linarith
  · obtain ⟨j, hj, hαj, h⟩ := of_chkA ck_F3 hα (by simpa using hα.1) (by
      have hq := qdn_le (1 / 10 : ℚ)
      have ht := (brk_bounds 5 le_rfl).2
      push_cast at hq ⊢
      simp only [topA, brk] at ht ⊢
      rw [sub_div]
      linarith)
    simp only [F3E, IE.eval_sub', IE.eval_mul', k, IE.eval_c, p1E_eval α j (by omega),
      envA_cos] at h
    rw [p₁_eq_closed (by omega) hαj]
    push_cast at h
    linarith

/-! ### (Q3): two points of `Cvx` at height `9/10` -/

def aRE (j : ℕ) : IE := k (7 / 20) * ecα + k (9 / 10) * esα - p1E j - k 1
def bRE (j : ℕ) : IE := -(k (7 / 20) * esα) + k (9 / 10) * ecα - p2E j - k 1
def aLE (j : ℕ) : IE := k (-8 / 5) * ecα + k (9 / 10) * esα - p1E j - k 1
def bLE (j : ℕ) : IE := -(k (-8 / 5) * esα) + k (9 / 10) * ecα - p2E j - k 1

theorem ck_aR : chkA aRE 14 0 topA = true := by
  decide +kernel

theorem ck_bR : chkA bRE 14 0 topA = true := by
  decide +kernel

theorem ck_aL : chkA aLE 14 0 topA = true := by
  decide +kernel

theorem ck_bL : chkA bLE 14 0 topA = true := by
  decide +kernel

/-! ## The geometry of the sofa -/

/-- The coordinates of `z` in the frame of the hallway at angle `α`. -/
def ca (α : ℝ) (z : ℝ²) : ℝ := ⟪z, u α⟫ - p₁ α

def cb (α : ℝ) (z : ℝ²) : ℝ := ⟪z, v α⟫ - p₂ α

lemma ca_pt (α a b : ℝ) : ca α (pt a b) = a * Real.cos α + b * Real.sin α - p₁ α := by
  rw [ca, inner_eq, pt_zero, pt_one, u_coord_zero, u_coord_one]

lemma cb_pt (α a b : ℝ) : cb α (pt a b) = -a * Real.sin α + b * Real.cos α - p₂ α := by
  rw [cb, inner_eq, pt_zero, pt_one, v_coord_zero, v_coord_one]; ring

lemma ca_eq (α : ℝ) (z : ℝ²) : ca α z = z 0 * Real.cos α + z 1 * Real.sin α - p₁ α := by
  rw [eq_pt z, ca_pt, pt_zero, pt_one]

lemma cb_eq (α : ℝ) (z : ℝ²) : cb α z = -z 0 * Real.sin α + z 1 * Real.cos α - p₂ α := by
  rw [eq_pt z, cb_pt, pt_zero, pt_one]

lemma mem_image_rotateTranslate {α : ℝ} {q z : ℝ²} {s : Set ℝ²} :
    z ∈ rotateTranslate (α : Real.Angle) q '' s ↔ rot (-α) z - q ∈ s := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [rotateTranslate_apply_eq_rot, rot_neg_rot, add_sub_cancel_right]
  · intro h
    refine ⟨rot (-α) z - q, h, ?_⟩
    rw [rotateTranslate_apply_eq_rot, sub_add_cancel, rot_rot, add_neg_cancel, rot_zero]

lemma frame_coords (α : ℝ) (z : ℝ²) :
    (rot (-α) z - GerversSofa.p α) 0 = ca α z ∧ (rot (-α) z - GerversSofa.p α) 1 = cb α z := by
  refine ⟨?_, ?_⟩
  · rw [PiLp.sub_apply, rot_neg_coord_zero, p_coord_zero]; rfl
  · rw [PiLp.sub_apply, rot_neg_coord_one, p_coord_one]; rfl

lemma mem_L_iff (α : ℝ) (z : ℝ²) :
    z ∈ rotateTranslate (α : Real.Angle) (GerversSofa.p α) '' hallway ↔
      (ca α z ≤ 1 ∧ cb α z ≤ 1) ∧ ¬(ca α z < 0 ∧ cb α z < 0) := by
  rw [mem_image_rotateTranslate, hallway_eq_diff]
  obtain ⟨h0, h1⟩ := frame_coords α z
  show ((rot (-α) z - GerversSofa.p α) 0 ≤ 1 ∧ (rot (-α) z - GerversSofa.p α) 1 ≤ 1) ∧
    ¬((rot (-α) z - GerversSofa.p α) 0 < 0 ∧ (rot (-α) z - GerversSofa.p α) 1 < 0) ↔ _
  rw [h0, h1]

lemma p_half : p₁ (π / 2) = 0 ∧ p₂ (π / 2) = 2 - 4 * GerversSofa.x 0 := by
  obtain ⟨p1, p2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  constructor
  · rw [p₁, if_neg (by linarith), sub_self, y_zero, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  · rw [p₂, if_neg (by linarith), Real.sin_pi_div_two]
    ring

lemma mem_H0_iff (z : ℝ²) :
    z ∈ rotateTranslate 0 (GerversSofa.p 0) '' horizontalHallway ↔
      z 0 ≤ 1 ∧ 0 ≤ z 1 ∧ z 1 ≤ 1 := by
  rw [← Real.Angle.coe_zero, mem_image_rotateTranslate, p_zero, neg_zero, sub_zero, rot_zero,
    mem_horizontalHallway_iff]

lemma mem_H1_iff (z : ℝ²) :
    z ∈ rotateTranslate ((π / 2 : ℝ) : Real.Angle) (GerversSofa.p (π / 2)) '' verticalHallway ↔
      0 ≤ z 1 ∧ z 1 ≤ 1 ∧ 4 * GerversSofa.x 0 - 3 ≤ z 0 := by
  rw [mem_image_rotateTranslate, mem_verticalHallway_iff]
  obtain ⟨h0, h1⟩ := frame_coords (π / 2) z
  rw [h0, h1, ca_eq, cb_eq, p_half.1, p_half.2, Real.cos_pi_div_two, Real.sin_pi_div_two]
  constructor
  · rintro ⟨a, b, c⟩; exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨a, b, c⟩; exact ⟨by linarith, by linarith, by linarith⟩

/-- The convex part of the constraints: outer walls, floor, ceiling and the left wall. -/
def Cvx : Set ℝ² := {z | (z 0 ≤ 1 ∧ 0 ≤ z 1 ∧ z 1 ≤ 1) ∧ 4 * GerversSofa.x 0 - 3 ≤ z 0 ∧
    ∀ α ∈ Icc (0 : ℝ) (π / 2), ca α z ≤ 1 ∧ cb α z ≤ 1}

lemma mem_Cvx {z : ℝ²} : z ∈ Cvx ↔ (z 0 ≤ 1 ∧ 0 ≤ z 1 ∧ z 1 ≤ 1) ∧
    4 * GerversSofa.x 0 - 3 ≤ z 0 ∧ ∀ α ∈ Icc (0 : ℝ) (π / 2), ca α z ≤ 1 ∧ cb α z ≤ 1 := Iff.rfl

/-- **Gerver's sofa** is `Cvx` minus the inner quadrants. -/
lemma mem_gerversSofa_iff {z : ℝ²} :
    z ∈ gerversSofa ↔ z ∈ Cvx ∧ ∀ α ∈ Icc (0 : ℝ) (π / 2), ¬(ca α z < 0 ∧ cb α z < 0) := by
  simp only [gerversSofa, sofaOfRotateTranslatePath, mem_inter_iff, mem_iInter₂, mem_H0_iff,
    mem_H1_iff, mem_L_iff]
  constructor
  · rintro ⟨⟨h0, h1⟩, h⟩
    exact ⟨mem_Cvx.2 ⟨h0, h1.2.2, fun α hα => (h α hα).1⟩, fun α hα => (h α hα).2⟩
  · rintro ⟨hC, h3⟩
    obtain ⟨h0, h1, h2⟩ := mem_Cvx.1 hC
    exact ⟨⟨h0, h0.2.1, h0.2.2, h1⟩, fun α hα => ⟨h2 α hα, h3 α hα⟩⟩

lemma combo_coord (z w : ℝ²) (a b : ℝ) (i : Fin 2) : (a • z + b • w) i = a * z i + b * w i := by
  simp [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

lemma convex_Cvx : Convex ℝ Cvx := by
  intro z hz w hw a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  obtain ⟨⟨z1, z2, z3⟩, z4, z5⟩ := mem_Cvx.1 hz
  obtain ⟨⟨w1, w2, w3⟩, w4, w5⟩ := mem_Cvx.1 hw
  have c0 := combo_coord z w a (1 - a) 0
  have c1 := combo_coord z w a (1 - a) 1
  refine mem_Cvx.2 ⟨⟨?_, ?_, ?_⟩, ?_, fun α hα => ⟨?_, ?_⟩⟩
  · rw [c0]; nlinarith
  · rw [c1]; nlinarith
  · rw [c1]; nlinarith
  · rw [c0]; nlinarith
  · have hz := (z5 α hα).1
    have hw := (w5 α hα).1
    rw [ca_eq] at hz hw ⊢
    rw [c0, c1]
    nlinarith [mul_le_mul_of_nonneg_left hz ha, mul_le_mul_of_nonneg_left hw hb]
  · have hz := (z5 α hα).2
    have hw := (w5 α hα).2
    rw [cb_eq] at hz hw ⊢
    rw [c0, c1]
    nlinarith [mul_le_mul_of_nonneg_left hz ha, mul_le_mul_of_nonneg_left hw hb]

lemma convex_coord_ge (i : Fin 2) (c : ℝ) : Convex ℝ {z : ℝ² | c ≤ z i} := by
  intro z hz w hw a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  show c ≤ (a • z + (1 - a) • w) i
  rw [combo_coord]
  have hz' : c ≤ z i := hz
  have hw' : c ≤ w i := hw
  nlinarith

lemma convex_coord_le (i : Fin 2) (c : ℝ) : Convex ℝ {z : ℝ² | z i ≤ c} := by
  intro z hz w hw a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  show (a • z + (1 - a) • w) i ≤ c
  rw [combo_coord]
  have hz' : z i ≤ c := hz
  have hw' : w i ≤ c := hw
  nlinarith

/-- (G1) The upper part `Cvx ∩ {y ≥ 9/10}` lies in the sofa. -/
lemma mem_of_high {z : ℝ²} (hz : z ∈ Cvx) (h : 9 / 10 ≤ z 1) : z ∈ gerversSofa := by
  refine mem_gerversSofa_iff.2 ⟨hz, fun α hα ⟨h1, h2⟩ => ?_⟩
  obtain ⟨hs, hc⟩ := sin_cos_nonneg hα.1 hα.2
  have hq := Q1 hα
  have hsc := Real.sin_sq_add_cos_sq α
  rw [ca_eq] at h1
  rw [cb_eq] at h2
  have e : z 1 = Real.sin α * (z 0 * Real.cos α + z 1 * Real.sin α)
      + Real.cos α * (-z 0 * Real.sin α + z 1 * Real.cos α) := by
    linear_combination (-z 1) * hsc
  have k1 : Real.sin α * (z 0 * Real.cos α + z 1 * Real.sin α) ≤ Real.sin α * p₁ α :=
    mul_le_mul_of_nonneg_left (by linarith) hs
  have k2 : Real.cos α * (-z 0 * Real.sin α + z 1 * Real.cos α) ≤ Real.cos α * p₂ α :=
    mul_le_mul_of_nonneg_left (by linarith) hc
  linarith

/-- (G2) The left end `Cvx ∩ {x ≤ −8/5}` lies in the sofa. -/
lemma mem_of_left {z : ℝ²} (hz : z ∈ Cvx) (h : z 0 ≤ -8 / 5) : z ∈ gerversSofa := by
  refine mem_gerversSofa_iff.2 ⟨hz, fun α hα hab => ?_⟩
  obtain ⟨-, h2⟩ := hab
  obtain ⟨hs, hc⟩ := sin_cos_nonneg hα.1 hα.2
  have hq := Q2L hα
  rw [cb_eq] at h2
  have hy := (mem_Cvx.1 hz).1.2.1
  have k1 : 0 ≤ z 1 * Real.cos α := mul_nonneg hy hc
  have k2 : 0 ≤ (-z 0 - 8 / 5) * Real.sin α := mul_nonneg (by linarith) hs
  nlinarith

/-- (G3) The right end `Cvx ∩ {x ≥ 7/20}` lies in the sofa. -/
lemma mem_of_right {z : ℝ²} (hz : z ∈ Cvx) (h : 7 / 20 ≤ z 0) : z ∈ gerversSofa := by
  refine mem_gerversSofa_iff.2 ⟨hz, fun α hα hab => ?_⟩
  obtain ⟨h1, -⟩ := hab
  obtain ⟨hs, hc⟩ := sin_cos_nonneg hα.1 hα.2
  have hq := Q2R hα
  rw [ca_eq] at h1
  have hy := (mem_Cvx.1 hz).1.2.1
  have k1 : 0 ≤ z 1 * Real.sin α := mul_nonneg hy hs
  have k2 : 0 ≤ (z 0 - 7 / 20) * Real.cos α := mul_nonneg (by linarith) hc
  nlinarith

/-- (G4) Moving a point of the sofa upwards inside `Cvx` stays in the sofa. -/
lemma up_mem {z w : ℝ²} (hz : z ∈ gerversSofa) (hw : w ∈ Cvx) (h0 : w 0 = z 0)
    (h1 : z 1 ≤ w 1) : w ∈ gerversSofa := by
  refine mem_gerversSofa_iff.2 ⟨hw, fun α hα ⟨k1, k2⟩ => ?_⟩
  obtain ⟨hs, hc⟩ := sin_cos_nonneg hα.1 hα.2
  refine (mem_gerversSofa_iff.1 hz).2 α hα ⟨?_, ?_⟩
  · rw [ca_eq] at k1 ⊢
    rw [h0] at k1
    nlinarith [mul_le_mul_of_nonneg_right h1 hs]
  · rw [cb_eq] at k2 ⊢
    rw [h0] at k2
    nlinarith [mul_le_mul_of_nonneg_right h1 hc]

/-- (G5) Two points of `Cvx` at height `9/10`. -/
lemma right_mem_Cvx : pt (7 / 20) (9 / 10) ∈ Cvx := by
  obtain ⟨x01, x02⟩ := x0_bounds
  refine mem_Cvx.2 ⟨⟨by norm_num, by norm_num, by norm_num⟩, by rw [pt_zero]; linarith,
    fun α hα => ⟨?_, ?_⟩⟩
  · obtain ⟨j, hj, hαj, h⟩ := of_chkA ck_aR hα (by simpa using hα.1) (mem_top hα).2
    simp only [aRE, IE.eval_sub', IE.eval_add', IE.eval_mul', k, IE.eval_c,
      p1E_eval α j (by omega), envA_sin, envA_cos] at h
    rw [ca_pt, p₁_eq_closed (by omega) hαj]
    push_cast at h
    linarith
  · obtain ⟨j, hj, hαj, h⟩ := of_chkA ck_bR hα (by simpa using hα.1) (mem_top hα).2
    simp only [bRE, IE.eval_sub', IE.eval_add', IE.eval_mul', IE.eval_neg', k, IE.eval_c,
      p2E_eval α j (by omega), envA_sin, envA_cos] at h
    rw [cb_pt, p₂_eq_closed (by omega) hαj]
    push_cast at h
    linarith

lemma left_mem_Cvx : pt (-8 / 5) (9 / 10) ∈ Cvx := by
  obtain ⟨x01, x02⟩ := x0_bounds
  refine mem_Cvx.2 ⟨⟨by norm_num, by norm_num, by norm_num⟩, by rw [pt_zero]; linarith,
    fun α hα => ⟨?_, ?_⟩⟩
  · obtain ⟨j, hj, hαj, h⟩ := of_chkA ck_aL hα (by simpa using hα.1) (mem_top hα).2
    simp only [aLE, IE.eval_sub', IE.eval_add', IE.eval_mul', k, IE.eval_c,
      p1E_eval α j (by omega), envA_sin, envA_cos] at h
    rw [ca_pt, p₁_eq_closed (by omega) hαj]
    push_cast at h
    linarith
  · obtain ⟨j, hj, hαj, h⟩ := of_chkA ck_bL hα (by simpa using hα.1) (mem_top hα).2
    simp only [bLE, IE.eval_sub', IE.eval_add', IE.eval_mul', IE.eval_neg', k, IE.eval_c,
      p2E_eval α j (by omega), envA_sin, envA_cos] at h
    rw [cb_pt, p₂_eq_closed (by omega) hαj]
    push_cast at h
    linarith

/-- (G6) The segment `[−8/5, 7/20] × {9/10}` lies in `Cvx`. -/
lemma mid_mem_Cvx {x : ℝ} (h1 : -8 / 5 ≤ x) (h2 : x ≤ 7 / 20) : pt x (9 / 10) ∈ Cvx := by
  have hab : (7 / 20 - x) / (39 / 20) + (x + 8 / 5) / (39 / 20) = 1 := by ring
  have h := convex_Cvx left_mem_Cvx right_mem_Cvx
    (div_nonneg (by linarith) (by norm_num) : (0 : ℝ) ≤ (7 / 20 - x) / (39 / 20))
    (div_nonneg (by linarith) (by norm_num) : (0 : ℝ) ≤ (x + 8 / 5) / (39 / 20)) hab
  have e : ((7 / 20 - x) / (39 / 20)) • pt (-8 / 5) (9 / 10)
      + ((x + 8 / 5) / (39 / 20)) • pt (7 / 20) (9 / 10) = pt x (9 / 10) := by
    ext i
    fin_cases i <;> simp <;> ring
  rwa [e] at h

/-- **Gerver's sofa is connected.** -/
theorem isConnected_gerversSofa : IsConnected gerversSofa := by
  have hb₀C := right_mem_Cvx
  have hb₀ : pt (7 / 20) (9 / 10) ∈ gerversSofa := mem_of_high hb₀C (by simp)
  set T : Set ℝ² := Cvx ∩ {z | 9 / 10 ≤ z 1} with hTdef
  have hT : T ⊆ gerversSofa := fun z hz => mem_of_high hz.1 hz.2
  have hTc : Convex ℝ T := convex_Cvx.inter (convex_coord_ge 1 _)
  have hb₀T : pt (7 / 20) (9 / 10) ∈ T := ⟨hb₀C, by simp⟩
  refine ⟨⟨_, hb₀⟩, isPreconnected_of_forall (pt (7 / 20) (9 / 10)) fun y hy => ?_⟩
  have hyC := (mem_gerversSofa_iff.1 hy).1
  by_cases h1 : 9 / 10 ≤ y 1
  · exact ⟨T, hT, hb₀T, ⟨hyC, h1⟩, hTc.isPreconnected⟩
  by_cases h2 : y 0 ≤ -8 / 5
  · have hL : pt (-8 / 5) (9 / 10) ∈ Cvx ∩ {z | z 0 ≤ -8 / 5} := ⟨left_mem_Cvx, by simp⟩
    refine ⟨(Cvx ∩ {z | z 0 ≤ -8 / 5}) ∪ T,
      union_subset (fun z hz => mem_of_left hz.1 hz.2) hT, Or.inr hb₀T, Or.inl ⟨hyC, h2⟩, ?_⟩
    exact (convex_Cvx.inter (convex_coord_le 0 _)).isPreconnected.union _ hL
      ⟨left_mem_Cvx, by simp⟩ hTc.isPreconnected
  by_cases h3 : 7 / 20 ≤ y 0
  · exact ⟨Cvx ∩ {z | 7 / 20 ≤ z 0}, fun z hz => mem_of_right hz.1 hz.2, ⟨hb₀C, by simp⟩,
      ⟨hyC, h3⟩, (convex_Cvx.inter (convex_coord_ge 0 _)).isPreconnected⟩
  push Not at h1 h2 h3
  have hwC : pt (y 0) (9 / 10) ∈ Cvx := mid_mem_Cvx h2.le h3.le
  refine ⟨segment ℝ y (pt (y 0) (9 / 10)) ∪ T, union_subset ?_ hT, Or.inr hb₀T,
    Or.inl (left_mem_segment ℝ _ _), ?_⟩
  · intro z hz
    have hzC := convex_Cvx.segment_subset hyC hwC hz
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    refine up_mem hy hzC ?_ ?_
    · rw [combo_coord, pt_zero]; linear_combination (y 0) * hab
    · rw [combo_coord, pt_one]
      have k1 : b * y 1 ≤ b * (9 / 10) := mul_le_mul_of_nonneg_left h1.le hb
      have k2 : a * y 1 + b * y 1 = y 1 := by linear_combination (y 1) * hab
      linarith
  · exact (convex_segment _ _).isPreconnected.union _ (right_mem_segment ℝ _ _)
      ⟨hwC, by simp⟩ hTc.isPreconnected

/-- **Gerver's sofa is a moving sofa** (the upstream `isMovingSofa_gerversSofa`, proved here;
the upstream file cannot import this proof, so its own statement keeps its `sorry`). -/
theorem isMovingSofa_gerversSofa' : ∃ m, IsMovingSofa gerversSofa m :=
  ⟨gmotion, isMovingSofa_gerversSofa_of_isConnected isConnected_gerversSofa⟩

end Sofa.GP
