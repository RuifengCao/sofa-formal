/-
# Sofa/ArmBound.lean — Baek §6.5: bounding the arm lengths

Given Thm 6.5.1 (`f_K` absolutely continuous with `f'_K ≥ m₀(g_K)`), §6.5 iterates the operator

    `F f (x) = 1 + ∫_0^x m₀(f(π/2 − u)) du`

eleven times from `f₀ = 0` and concludes `f_K, g_K > 1`.  Everything in this file is
**self-contained real analysis**: the iteration, the comparison functions `j_c(x) = max(1−x, c)`,
and the two quadratic inequalities in `π` that make `F j_c ≥ j_{c+1/12}` work.

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.Injective

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

/-! ## Continuity and elementary bounds for `m₀` -/

lemma continuous_m0 : Continuous m0 := continuous_id.sub continuous_k0

lemma neg_one_le_m0 {x : ℝ} (hx : 0 ≤ x) : -1 ≤ m0 x := by
  have := m0_mono hx
  rwa [m0_zero] at this

lemma zero_lt_m0 {x : ℝ} (hx : 2 / 3 < x) : 0 < m0 x := by
  have h1 : m0 (2 / 3) = 0 := by rw [m0_of_le_one (by norm_num) (by norm_num)]; ring
  have h2 : m0 (2 / 3) ≤ m0 x := m0_mono hx.le
  rcases eq_or_lt_of_le h2 with heq | hlt
  · exfalso
    -- `m₀` is strictly increasing on `[0,1]`, so equality forces `x > 1`, where `m₀ x ≥ 1/2 > 0`
    rcases le_or_gt x 1 with h | h
    · rw [m0_of_le_one (by linarith) h, h1] at heq; linarith
    · have := m0_mono h.le
      rw [m0_one] at this
      rw [← heq, h1] at this; linarith
  · rw [h1] at hlt; exact hlt

/-! ## The operator `F` (Def 6.5.1) -/

lemma continuous_primitive {G : ℝ → ℝ} (hG : Continuous G) (a : ℝ) :
    Continuous fun x => ∫ u in a..x, G u := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => ∫ u in a..x, G u) (G x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable (μ := volume) a x)
      (hG.stronglyMeasurableAtFilter _ _) hG.continuousAt
  exact Differentiable.continuous (𝕜 := ℝ) fun x => (hd x).differentiableAt

/-- **Def 6.5.1.** -/
def armF (f : ℝ → ℝ) (x : ℝ) : ℝ := 1 + ∫ u in (0:ℝ)..x, m0 (f (π / 2 - u))

lemma continuous_armF {f : ℝ → ℝ} (hf : Continuous f) : Continuous (armF f) := by
  have hG : Continuous fun u : ℝ => m0 (f (π / 2 - u)) :=
    continuous_m0.comp (hf.comp (continuous_const.sub continuous_id))
  exact continuous_const.add (continuous_primitive hG 0)

/-- `F f ≥ 1 − x`, because `m₀ ≥ −1` on the nonnegative reals. -/
lemma one_sub_le_armF {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ y, 0 ≤ f y) {x : ℝ}
    (hx0 : 0 ≤ x) : 1 - x ≤ armF f x := by
  have hG : Continuous fun u : ℝ => m0 (f (π / 2 - u)) :=
    continuous_m0.comp (hf.comp (continuous_const.sub continuous_id))
  have hle : ∫ u in (0:ℝ)..x, (-1 : ℝ) ≤ ∫ u in (0:ℝ)..x, m0 (f (π / 2 - u)) :=
    intervalIntegral.integral_mono_on hx0
      (intervalIntegrable_const (μ := volume) (c := (-1 : ℝ)))
      (hG.intervalIntegrable (μ := volume) 0 x) fun u _ => neg_one_le_m0 (hf0 _)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle
  rw [armF]; linarith

/-- **Lemma 6.5.4.** -/
lemma armF_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hle : ∀ y ∈ Icc 0 (π / 2), f y ≤ g y) {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ π / 2) :
    armF f x ≤ armF g x := by
  have hGf : Continuous fun u : ℝ => m0 (f (π / 2 - u)) :=
    continuous_m0.comp (hf.comp (continuous_const.sub continuous_id))
  have hGg : Continuous fun u : ℝ => m0 (g (π / 2 - u)) :=
    continuous_m0.comp (hg.comp (continuous_const.sub continuous_id))
  have := intervalIntegral.integral_mono_on hx0 (hGf.intervalIntegrable (μ := volume) 0 x)
    (hGg.intervalIntegrable (μ := volume) 0 x) fun u hu =>
      m0_mono (hle _ ⟨by linarith [hu.2], by linarith [hu.1]⟩)
  rw [armF, armF]; linarith

/-! ## The iterates (Def 6.5.2) -/

/-- **Def 6.5.2.** -/
def armIter : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => max (armIter n x) (armF (armIter n) x)

lemma continuous_armIter : ∀ n : ℕ, Continuous (armIter n)
  | 0 => continuous_const
  | n + 1 => (continuous_armIter n).max (continuous_armF (continuous_armIter n))

lemma armIter_le_succ (n : ℕ) (x : ℝ) : armIter n x ≤ armIter (n + 1) x := le_max_left _ _

lemma armF_le_succ (n : ℕ) (x : ℝ) : armF (armIter n) x ≤ armIter (n + 1) x := le_max_right _ _

lemma armIter_nonneg : ∀ (n : ℕ) (x : ℝ), 0 ≤ armIter n x
  | 0, _ => le_rfl
  | n + 1, x => le_trans (armIter_nonneg n x) (armIter_le_succ n x)

/-! ## The comparison functions `j_c` (Def 6.5.3) and Lemma 6.5.3 -/

/-- **Def 6.5.3.** -/
def jFn (c x : ℝ) : ℝ := max (1 - x) c

lemma continuous_jFn (c : ℝ) : Continuous (jFn c) :=
  (continuous_const.sub continuous_id).max continuous_const

lemma jFn_nonneg {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : 0 ≤ jFn c x := le_trans hc (le_max_right _ _)

private lemma integral_max_left {c x : ℝ} (hx0 : 0 ≤ x) (hxa : x ≤ π / 2 - 1 + c) :
    ∫ u in (0:ℝ)..x, max (u + 1 - π / 2) c = c * x := by
  have heq : ∀ u ∈ uIcc (0:ℝ) x, max (u + 1 - π / 2) c = c := by
    intro u hu
    rw [uIcc_of_le hx0] at hu
    exact max_eq_right (by linarith [hu.2])
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  ring

private lemma integral_max_right {c x : ℝ} (hc0 : 0 ≤ c) (hax : π / 2 - 1 + c ≤ x) :
    ∫ u in (0:ℝ)..x, max (u + 1 - π / 2) c
      = c * (π / 2 - 1 + c) + ((x + 1 - π / 2) ^ 2 - c ^ 2) / 2 := by
  have hpi := pi_gt_three
  have ha0 : (0:ℝ) ≤ π / 2 - 1 + c := by linarith
  have hcont : Continuous fun u : ℝ => max (u + 1 - π / 2) c := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 (π / 2 - 1 + c))
    (hcont.intervalIntegrable (μ := volume) (π / 2 - 1 + c) x),
    integral_max_left ha0 le_rfl]
  have heq : ∀ u ∈ uIcc (π / 2 - 1 + c) x, max (u + 1 - π / 2) c = u + (1 - π / 2) := by
    intro u hu
    rw [uIcc_of_le hax] at hu
    rw [max_eq_left (by linarith [hu.1])]; ring
  rw [intervalIntegral.integral_congr heq,
    intervalIntegral.integral_add intervalIntegral.intervalIntegrable_id
      (intervalIntegrable_const (μ := volume) (c := 1 - π / 2)),
    integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **Lemma 6.5.3.** `F j_c ≥ j_{c + 1/12}` for `c ∈ [0, 2/3]`. -/
theorem jFn_le_armF {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2 / 3) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ π / 2) : jFn (c + 1 / 12) x ≤ armF (jFn c) x := by
  have hpi1 : (3.14 : ℝ) < π := pi_gt_d2
  have hpi2 : π < 3.15 := pi_lt_d2
  refine max_le (one_sub_le_armF (continuous_jFn c) (fun y => jFn_nonneg hc0 y) hx0) ?_
  -- rewrite the integral of `m₀ ∘ j_c ∘ (π/2 − ·)`
  have hcont : Continuous fun u : ℝ => max (u + 1 - π / 2) c := by fun_prop
  have hint : ∫ u in (0:ℝ)..x, m0 (jFn c (π / 2 - u))
      = 3 / 2 * (∫ u in (0:ℝ)..x, max (u + 1 - π / 2) c) - x := by
    have heq : ∀ u ∈ uIcc (0:ℝ) x,
        m0 (jFn c (π / 2 - u)) = 3 / 2 * max (u + 1 - π / 2) c - 1 := by
      intro u hu
      rw [uIcc_of_le hx0] at hu
      have hj : jFn c (π / 2 - u) = max (u + 1 - π / 2) c := by
        rw [jFn]; congr 1; ring
      have h0 : 0 ≤ max (u + 1 - π / 2) c := le_trans hc0 (le_max_right _ _)
      have h1 : max (u + 1 - π / 2) c ≤ 1 :=
        max_le (by linarith [hu.2]) (by linarith)
      rw [hj, m0_of_le_one h0 h1]; ring
    rw [intervalIntegral.integral_congr heq,
      intervalIntegral.integral_sub (hcont.intervalIntegrable (μ := volume) 0 x |>.const_mul _)
        (intervalIntegrable_const (μ := volume) (c := (1:ℝ))),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    ring
  rw [armF, hint]
  rcases le_or_gt x (π / 2 - 1 + c) with hcase | hcase
  · rw [integral_max_left hx0 hcase]
    have h1 : 0 ≤ (π / 2 - 1 + c - x) * (1 - 3 * c / 2) :=
      mul_nonneg (by linarith) (by linarith)
    have h3 : 0 < -(1/8 : ℝ) + 3 * π / 8 - 3 * π ^ 2 / 32 := by nlinarith [hpi1, hpi2]
    nlinarith [h1, h3, sq_nonneg (c - (7 / 6 - π / 4))]
  · rw [integral_max_right hc0 hcase.le]
    have h4 : 0 < -(1/2 : ℝ) + 3 * π / 4 - 3 * π ^ 2 / 16 := by nlinarith [hpi1, hpi2]
    nlinarith [h4, sq_nonneg (x - (π / 2 - 1 / 3)), sq_nonneg (c - (5 / 3 - π / 2))]

/-! ## The iteration (Lemma 6.5.5) -/

lemma armF_zero (x : ℝ) : armF (fun _ => (0:ℝ)) x = 1 - x := by
  rw [armF]
  simp only [m0_zero]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  ring

lemma armIter_one (x : ℝ) : armIter 1 x = jFn 0 x := by
  show max (armIter 0 x) (armF (armIter 0) x) = jFn 0 x
  rw [show armIter 0 = (fun _ : ℝ => (0:ℝ)) from rfl, armF_zero, jFn, max_comm]

private lemma iter_step {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 2 / 3) {n : ℕ}
    (hn : ∀ y ∈ Icc (0:ℝ) (π / 2), jFn c y ≤ armIter n y) :
    ∀ y ∈ Icc (0:ℝ) (π / 2), jFn (c + 1 / 12) y ≤ armIter (n + 1) y := by
  intro y hy
  calc jFn (c + 1 / 12) y ≤ armF (jFn c) y := jFn_le_armF hc0 hc hy.1 hy.2
    _ ≤ armF (armIter n) y := armF_mono (continuous_jFn c) (continuous_armIter n) hn hy.1 hy.2
    _ ≤ armIter (n + 1) y := armF_le_succ n y

private lemma iter_ge : ∀ k : ℕ, k ≤ 9 →
    ∀ y ∈ Icc (0:ℝ) (π / 2), jFn ((k : ℝ) / 12) y ≤ armIter (k + 1) y := by
  intro k
  induction k with
  | zero => intro _ y _; rw [Nat.cast_zero, zero_div, armIter_one]
  | succ n ih =>
    intro hn y hy
    have hstep := iter_step (c := (n : ℝ) / 12) (by positivity)
      (by
        have : (n : ℝ) ≤ 8 := by exact_mod_cast (by omega : n ≤ 8)
        linarith) (ih (by omega)) y hy
    rwa [show (n : ℝ) / 12 + 1 / 12 = ((n : ℕ) + 1 : ℕ) / 12 from by push_cast; ring] at hstep

/-- **Lemma 6.5.5.** -/
theorem one_lt_armIter_eleven {x : ℝ} (hx0 : 0 < x) (hx : x ≤ π / 2) : 1 < armIter 11 x := by
  have hpi := pi_gt_three
  have h10 : ∀ y ∈ Icc (0:ℝ) (π / 2), (3:ℝ) / 4 ≤ armIter 10 y := by
    intro y hy
    have h := iter_ge 9 le_rfl y hy
    have hj : ((9:ℕ) : ℝ) / 12 ≤ jFn (((9:ℕ) : ℝ) / 12) y := le_max_right _ _
    have h9 : ((9:ℕ) : ℝ) / 12 = 3 / 4 := by norm_num
    rw [h9] at hj
    have h10' : armIter (9 + 1) y = armIter 10 y := rfl
    rw [h10'] at h
    linarith
  have hG : Continuous fun u : ℝ => m0 (armIter 10 (π / 2 - u)) :=
    continuous_m0.comp ((continuous_armIter 10).comp (continuous_const.sub continuous_id))
  have hlow : ∀ u ∈ Icc (0:ℝ) x, (1:ℝ) / 8 ≤ m0 (armIter 10 (π / 2 - u)) := by
    intro u hu
    have hmem : π / 2 - u ∈ Icc (0:ℝ) (π / 2) := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have h1 : (3:ℝ) / 4 ≤ armIter 10 (π / 2 - u) := h10 _ hmem
    have h2 : m0 (3 / 4 : ℝ) = 1 / 8 := by
      rw [m0_of_le_one (by norm_num) (by norm_num)]; ring
    have := m0_mono h1
    rwa [h2] at this
  have hbound : (1:ℝ) / 8 * x ≤ ∫ u in (0:ℝ)..x, m0 (armIter 10 (π / 2 - u)) := by
    have := intervalIntegral.integral_mono_on hx0.le
      (intervalIntegrable_const (μ := volume) (c := (1:ℝ) / 8))
      (hG.intervalIntegrable (μ := volume) 0 x) hlow
    rwa [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm] at this
  have hF : 1 < armF (armIter 10) x := by
    rw [armF]; nlinarith [hbound, hx0]
  exact lt_of_lt_of_le hF (armF_le_succ 10 x)

/-! ## Lemma 6.5.2 and Theorem 6.5.6, conditionally on Theorem 6.5.1

`ArmPair f G` packages what §6.5 needs about a balanced maximum cap `K`: with
`f = f_K` and `G = fun t => g_K(π/2 − t)` (the arm lengths of the mirror image `K^m`),
Theorem 6.5.1 plus `f_K(0) ≥ 1` give exactly the two integral bounds below — and the mirror
symmetry `f_{K^m}(t) = g_K(π/2 − t)` is what makes the pair *symmetric* in `f` and `G`. -/
structure ArmPair (f G : ℝ → ℝ) : Prop where
  cont_f : Continuous f
  cont_G : Continuous G
  nonneg_f : ∀ y, 0 ≤ f y
  nonneg_G : ∀ y, 0 ≤ G y
  /-- Thm 6.5.1 for `K`, integrated, with `f_K(0) ≥ 1`. -/
  bound_f : ∀ t ∈ Icc (0:ℝ) (π / 2), 1 + ∫ u in (0:ℝ)..t, m0 (G (π / 2 - u)) ≤ f t
  /-- Thm 6.5.1 for the mirror image `K^m`. -/
  bound_G : ∀ t ∈ Icc (0:ℝ) (π / 2), 1 + ∫ u in (0:ℝ)..t, m0 (f (π / 2 - u)) ≤ G t

/-- **Lemma 6.5.2.** -/
theorem armIter_le_of_armPair {f G : ℝ → ℝ} (h : ArmPair f G) (n : ℕ) :
    ∀ t ∈ Icc (0:ℝ) (π / 2), armIter n t ≤ f t ∧ armIter n t ≤ G t := by
  induction n with
  | zero => exact fun t _ => ⟨h.nonneg_f t, h.nonneg_G t⟩
  | succ n ih =>
    intro t ht
    refine ⟨max_le (ih t ht).1 ?_, max_le (ih t ht).2 ?_⟩
    · exact le_trans (armF_mono (continuous_armIter n) h.cont_G (fun y hy => (ih y hy).2)
        ht.1 ht.2) (h.bound_f t ht)
    · exact le_trans (armF_mono (continuous_armIter n) h.cont_f (fun y hy => (ih y hy).1)
        ht.1 ht.2) (h.bound_G t ht)

/-- **Theorem 6.5.6** (conditional on Theorem 6.5.1, packaged as `ArmPair`):
`f_K(t) > 1` on `(0, π/2]` and `g_K(s) > 1` on `[0, π/2)`. -/
theorem one_lt_of_armPair {f G : ℝ → ℝ} (h : ArmPair f G) {t : ℝ} (ht0 : 0 < t)
    (ht : t ≤ π / 2) : 1 < f t ∧ 1 < G t := by
  have hle := armIter_le_of_armPair h 11 t ⟨ht0.le, ht⟩
  have h11 := one_lt_armIter_eleven ht0 ht
  exact ⟨lt_of_lt_of_le h11 hle.1, lt_of_lt_of_le h11 hle.2⟩

/-! ## Theorem 6.5.1 in integrated form

Baek deduces Thm 6.5.1 from Thm 6.4.3 through the Radon–Nikodym theorem (Cor 6.4.4), the
density `r_K`, and Prop 5.1.4 (absolute continuity).  None of that is needed: Theorem 6.2.5
already gives `σ_K((a,b]) = ∫_a^b g⁺_K − (f⁺_K(b) − f⁺_K(a))` as an *identity*, so the measure
inequality `σ_K ≤ k₀(g_K) dt` of Thm 6.4.3 turns into the integrated differential inequality in
one line. -/
theorem armFp_ge_of_sigmaK_le {K : Set ℝ²} (hK : IsCompact K) (hne : K.Nonempty) {T : ℝ}
    (hgi : IntervalIntegrable (fun s => armGp K s) volume 0 T)
    (hki : IntervalIntegrable (fun s => k0 (armGp K s)) volume 0 T)
    (hσ : (sigmaK K (Ioc 0 T)).toReal ≤ ∫ s in (0:ℝ)..T, k0 (armGp K s)) (hT : 0 ≤ T) :
    armFp K 0 + ∫ s in (0:ℝ)..T, m0 (armGp K s) ≤ armFp K T := by
  have hid := sigmaK_Ioc_toReal_eq hK hne hT
  have hsplit : ∫ s in (0:ℝ)..T, m0 (armGp K s)
      = (∫ s in (0:ℝ)..T, armGp K s) - ∫ s in (0:ℝ)..T, k0 (armGp K s) := by
    rw [← intervalIntegral.integral_sub hgi hki]
    rfl
  rw [hsplit]
  linarith
