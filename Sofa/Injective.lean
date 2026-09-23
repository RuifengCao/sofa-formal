/-
# Sofa/Injective.lean — Baek Def 6.1.2 (the injectivity condition) and Def 6.3.4 (`k₀`, `m₀`)

**Def 6.1.2** says a cap `K` with rotation angle `π/2` is *injective* if

1. `σ_K` is absolutely continuous on `[0, π/2)` and on `(π/2, π]`;
2. the inner corner `x_K` is continuously differentiable on `[0, π/2]`;
3. `⟪x'_K(t), u_t⟫ < 0 < ⟪x'_K(t), v_t⟫` for `t ∈ (0, π/2)`.

By **Thm 6.2.3** (`Sofa/ArmLength.lean`) the right derivative of `x_K` is
`(1 − f⁺_K(t)) u_t + (g⁺_K(t) − 1) v_t`, so (2) is the continuity of the arm lengths and (3) is
exactly `f⁺_K(t) > 1` and `g⁺_K(t) > 1` — which is how they are stated here.

**Which arm length is the continuous one.**  Baek's Definition 6.4.1 sets
`f_K(t) := f⁺_K(t) = f⁻_K(t)` for `t ∈ [0, π/2)` and `f_K(π/2) := f⁻_K(π/2)`, and dually
`g_K(t) := g⁺_K(t) = g⁻_K(t)` for `t ∈ (0, π/2]` and `g_K(0) := g⁺_K(0)`; Proposition 6.4.6 (1)
then says `f_K` and `g_K` are continuous on `[0, π/2]`.  So `f_K = f⁻_K = armFm` on the *closed*
interval and `g_K = g⁺_K = armGp` on the closed interval.  This matters: `σ_K` is allowed an atom
at `t = π/2` (the cap's top face, which is a genuine segment for Gerver's sofa), and there
`f⁺_K(π/2) = f⁻_K(π/2) − |e_K(π/2)| < f⁻_K(π/2)`, so `f⁺_K` is *not* left-continuous at `π/2`.
Stating (2) with `armFp` on `Icc 0 (π/2)` would therefore be a condition no interesting cap
satisfies.

STATUS: [PROOF-C-local] round 2 (2026-09-22, Opus 5).  `IsInjectiveCap` is a *definition*;
Thm 6.1.1 (balanced maximum caps are injective) is proved in `Sofa/AbsCont.lean`.
-/
import Sofa.ArmLength

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²}

/-! ## Definition 6.1.2 -/

/-- **Baek Definition 6.1.2**: the injectivity condition for a cap of rotation angle `π/2`. -/
structure IsInjectiveCap (K : Set ℝ²) : Prop where
  /-- `K` is a cap with rotation angle `π/2`. -/
  isCap : IsCap K (π / 2)
  /-- (1) `σ_K` is absolutely continuous on `[0, π/2)`. -/
  ac_left : (sigmaK K).restrict (Ico 0 (π / 2)) ≪ volume
  /-- (1) `σ_K` is absolutely continuous on `(π/2, π]`. -/
  ac_right : (sigmaK K).restrict (Ioc (π / 2) π) ≪ volume
  /-- (2) `x_K ∈ C¹`: Baek's `f_K` (Def 6.4.1), which is `f⁻_K`, is continuous on `[0, π/2]`. -/
  continuousOn_armFm : ContinuousOn (armFm K) (Icc 0 (π / 2))
  /-- (2) `x_K ∈ C¹`: Baek's `g_K` (Def 6.4.1), which is `g⁺_K`, is continuous on `[0, π/2]`. -/
  continuousOn_armGp : ContinuousOn (armGp K) (Icc 0 (π / 2))
  /-- (3) `⟪x'_K(t), u_t⟫ < 0 < ⟪x'_K(t), v_t⟫`. -/
  one_lt_arm : ∀ t ∈ Ioo (0 : ℝ) (π / 2), 1 < armFp K t ∧ 1 < armGp K t

/-- Condition (3) of Def 6.1.2, in the form Baek states it. -/
theorem IsInjectiveCap.inner_deriv_innerCorner (h : IsInjectiveCap K) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (π / 2)) :
    ⟪(1 - armFp K t) • u t + (armGp K t - 1) • v t, u t⟫ < 0 ∧
      0 < ⟪(1 - armFp K t) • u t + (armGp K t - 1) • v t, v t⟫ := by
  obtain ⟨hf, hg⟩ := h.one_lt_arm t ht
  obtain ⟨e1, e2⟩ := inner_innerCorner_deriv K t
  rw [e1, e2]
  constructor <;> linarith

/-! ## Definition 6.3.4 -/

/-- `k₀(x) = max(|x − 1|, (|x − 1| + 1)/2)`. -/
def k0 (x : ℝ) : ℝ := max |x - 1| ((|x - 1| + 1) / 2)

lemma continuous_k0 : Continuous k0 := by
  unfold k0
  fun_prop

/-- `m₀(x) = x − k₀(x)`. -/
def m0 (x : ℝ) : ℝ := x - k0 x

lemma abs_le_k0 (x : ℝ) : |x - 1| ≤ k0 x := le_max_left _ _

lemma half_le_k0 (x : ℝ) : (|x - 1| + 1) / 2 ≤ k0 x := le_max_right _ _

lemma k0_nonneg (x : ℝ) : 0 ≤ k0 x := le_trans (abs_nonneg _) (abs_le_k0 x)

/-- `k₀` is 1-Lipschitz from above along increasing `x`. -/
lemma k0_le_add {x y : ℝ} (hxy : x ≤ y) : k0 y ≤ k0 x + (y - x) := by
  have habs : |y - 1| ≤ |x - 1| + (y - x) := by
    have h := abs_sub_abs_le_abs_sub (y - 1) (x - 1)
    rw [show y - 1 - (x - 1) = y - x by ring,
      abs_of_nonneg (show (0:ℝ) ≤ y - x by linarith)] at h
    linarith
  refine max_le ?_ ?_
  · linarith [abs_le_k0 x]
  · linarith [half_le_k0 x]

/-- `m₀` is monotone. -/
theorem m0_mono : Monotone m0 := by
  intro x y hxy
  have := k0_le_add hxy
  rw [m0, m0]
  linarith

/-! ### The explicit piecewise-linear form of `m₀` -/

lemma k0_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) : k0 x = 1 - x / 2 := by
  have habs : |x - 1| = 1 - x := by rw [abs_of_nonpos (by linarith)]; ring
  rw [k0, habs]
  rw [max_eq_right (by linarith)]
  ring

lemma k0_of_mem_Icc_one_two {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) : k0 x = x / 2 := by
  have habs : |x - 1| = x - 1 := abs_of_nonneg (by linarith)
  rw [k0, habs, max_eq_right (by linarith)]
  ring

lemma k0_of_two_le {x : ℝ} (hx : 2 ≤ x) : k0 x = x - 1 := by
  have habs : |x - 1| = x - 1 := abs_of_nonneg (by linarith)
  rw [k0, habs, max_eq_left (by linarith)]

theorem m0_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) : m0 x = 3 * x / 2 - 1 := by
  rw [m0, k0_of_le_one hx0 hx]; ring

theorem m0_of_mem_Icc_one_two {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2) : m0 x = x / 2 := by
  rw [m0, k0_of_mem_Icc_one_two hx1 hx2]; ring

theorem m0_of_two_le {x : ℝ} (hx : 2 ≤ x) : m0 x = 1 := by
  rw [m0, k0_of_two_le hx]; ring

@[simp] theorem m0_zero : m0 0 = -1 := by rw [m0_of_le_one le_rfl zero_le_one]; ring

@[simp] theorem m0_one : m0 1 = 1 / 2 := by rw [m0_of_le_one zero_le_one le_rfl]; ring

theorem m0_le_one (x : ℝ) : m0 x ≤ 1 := by
  rcases le_or_gt x 2 with h | h
  · rcases le_or_gt x 1 with h1 | h1
    · rcases le_or_gt 0 x with h0 | h0
      · rw [m0_of_le_one h0 h1]; linarith
      · have := m0_mono (le_of_lt h0 : x ≤ 0)
        simp only [m0_zero] at this
        linarith
    · rw [m0_of_mem_Icc_one_two h1.le h]; linarith
  · rw [m0_of_two_le h.le]

end Sofa
