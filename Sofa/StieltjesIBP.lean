/-
# Sofa/StieltjesIBP.lean — integration by parts against a Stieltjes measure

For a Stieltjes function `F` and a function `g` that is absolutely continuous on `[a, b]`,

    `∫_{(a,b]} g dF = g(b) F(b) − g(a) F(a) − ∫_a^b g'(s) F(s) ds`.

Mathlib has integration by parts for two absolutely continuous functions
(`AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul`), but not against a Stieltjes
measure.  The proof here is Fubini on the triangle `{a < s < t ≤ b}` for `ds ⊗ dF(t)`:

    `∫_{(a,b]} (g(t) − g(a)) dF(t) = ∫_{(a,b]} ∫_{(a,t)} g'(s) ds dF(t)
                                   = ∫_{(a,b]} g'(s) F((s,b]) ds = ∫_a^b g'(s) (F(b) − F(s)) ds`.

This is the one analytic tool that Baek's Chapter 7 needs beyond what the project already has:
it turns `½∫ h_K dσ_K` into the classical `½[h·h']  + ½∫(h² − h'²)` (`Sofa/CurveArea.lean`),
from which Mamikon's theorem is a two-line computation (`Sofa/Mamikon.lean`).

STATUS: [PROOF-C-local] round 1 (2026-09-22, Opus 5.5).
-/
import Mathlib

noncomputable section

open Set Filter MeasureTheory

namespace Sofa

/-- **Integration by parts against a Stieltjes measure.** -/
theorem integral_Ioc_stieltjes (F : StieltjesFunction ℝ) {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    ∫ t in Ioc a b, g t ∂F.measure
      = g b * F b - g a * F a - ∫ s in a..b, deriv g s * F s := by
  -- the two finite measures
  set μ : Measure ℝ := F.measure.restrict (Ioc a b) with hμ
  set ν : Measure ℝ := volume.restrict (Ioc a b) with hν
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [hμ, Measure.restrict_apply_univ, F.measure_Ioc]
    exact ENNReal.ofReal_lt_top
  have : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hν, Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  have hg' : IntervalIntegrable (deriv g) volume a b := hg.intervalIntegrable_deriv
  have hg'ν : Integrable (deriv g) ν := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hg'
  have hgc : ContinuousOn g (Icc a b) := by
    have := hg.continuousOn; rwa [uIcc_of_le hab] at this
  -- the kernel `f t s = 1_{s < t} g'(s)`
  set f : ℝ → ℝ → ℝ := fun t s => (Iio t).indicator (deriv g) s with hf
  have hfm : Measurable (Function.uncurry f) := by
    have e : Function.uncurry f = fun p : ℝ × ℝ => if p.2 < p.1 then deriv g p.2 else 0 := by
      funext p
      simp only [Function.uncurry, hf, Set.indicator_apply, mem_Iio]
    rw [e]
    exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
      ((measurable_deriv g).comp measurable_snd) measurable_const
  have hfint : Integrable (Function.uncurry f) (μ.prod ν) := by
    have hdom : Integrable (fun p : ℝ × ℝ => (1:ℝ) * |deriv g p.2|) (μ.prod ν) :=
      (integrable_const (1:ℝ)).mul_prod hg'ν.abs
    refine hdom.mono' hfm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, hf, one_mul, Real.norm_eq_abs]
    by_cases hp : p.2 ∈ Iio p.1
    · rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, abs_zero]; exact abs_nonneg _
  -- inner integral in `s`: `∫_{(a,b]} 1_{s<t} g'(s) ds = g(t) − g(a)`
  have hin1 : EqOn (fun t => g t - g a) (fun t => ∫ s, f t s ∂ν) (Ioc a b) := by
    intro t ht
    simp only [hf, hν]
    rw [setIntegral_indicator measurableSet_Iio,
      show Ioc a b ∩ Iio t = Ioo a t by
        ext x; simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by linarith [ht.2]⟩, h3⟩,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.1.le]
    have hac : AbsolutelyContinuousOnInterval g a t :=
      hg.mono (uIcc_subset_uIcc (left_mem_uIcc) (by
        rw [uIcc_of_le hab]; exact ⟨ht.1.le, ht.2⟩))
    rw [hac.integral_deriv_eq_sub]
  -- inner integral in `t`: `∫_{(a,b]} 1_{s<t} g'(s) dF(t) = g'(s) (F(b) − F(s))`
  have hin2 : EqOn (fun s => deriv g s * (F b - F s)) (fun s => ∫ t, f t s ∂μ) (Ioc a b) := by
    intro s hs
    have e : (fun t => f t s) = (Ioi s).indicator (fun _ => deriv g s) := by
      funext t
      simp only [hf, Set.indicator_apply, mem_Iio, mem_Ioi]
    simp only [hμ]
    rw [e, setIntegral_indicator measurableSet_Ioi,
      show Ioc a b ∩ Ioi s = Ioc s b by
        ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
        constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith [hs.1], h2⟩, h1⟩,
      setIntegral_const, smul_eq_mul, Measure.real, F.measure_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.2 (F.mono hs.2)), mul_comm]
  -- integrability of `g` against `dF` and of `g' F` against `ds`
  have hgμ : Integrable g μ :=
    (hgc.integrableOn_compact (μ := F.measure) isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hFbd : ∀ s ∈ Ioc a b, ‖F s‖ ≤ max |F a| |F b| := by
    intro s hs
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h1 := F.mono hs.1.le
      have h2 := neg_abs_le (F a)
      have h3 := le_max_left |F a| |F b|
      linarith
    · have h1 := F.mono hs.2
      have h2 := le_abs_self (F b)
      have h3 := le_max_right |F a| |F b|
      linarith
  have hg'F : Integrable (fun s => deriv g s * F s) ν := by
    refine hg'ν.mul_bdd (c := max |F a| |F b|) (F.mono.measurable.aestronglyMeasurable) ?_
    exact (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hFbd)
  -- Fubini
  have hswap := integral_integral_swap hfint
  have hL : ∫ t, (g t - g a) ∂μ = ∫ t, ∫ s, f t s ∂ν ∂μ :=
    setIntegral_congr_fun measurableSet_Ioc hin1
  have hR : ∫ s, deriv g s * (F b - F s) ∂ν = ∫ s, ∫ t, f t s ∂μ ∂ν :=
    setIntegral_congr_fun measurableSet_Ioc hin2
  -- unfold both sides
  have hL' : ∫ t, (g t - g a) ∂μ = (∫ t, g t ∂μ) - g a * (F b - F a) := by
    rw [integral_sub hgμ (integrable_const _), integral_const, smul_eq_mul, hμ,
      Measure.real, Measure.restrict_apply_univ, F.measure_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.2 (F.mono hab)), mul_comm]
  have hR' : ∫ s, deriv g s * (F b - F s) ∂ν
      = F b * (g b - g a) - ∫ s in a..b, deriv g s * F s := by
    have e1 : (fun s => deriv g s * (F b - F s)) = fun s => F b * deriv g s - deriv g s * F s := by
      funext s; ring
    rw [e1, integral_sub (hg'ν.const_mul (F b)) hg'F, integral_const_mul]
    have e2 : ∫ s, deriv g s ∂ν = g b - g a := by
      rw [hν, ← intervalIntegral.integral_of_le hab, hg.integral_deriv_eq_sub]
    have e3 : ∫ s, deriv g s * F s ∂ν = ∫ s in a..b, deriv g s * F s := by
      rw [hν, intervalIntegral.integral_of_le hab]
    rw [e2, e3]
  have hmain : (∫ t, g t ∂μ) - g a * (F b - F a)
      = F b * (g b - g a) - ∫ s in a..b, deriv g s * F s := by
    rw [← hL', ← hR', hL, hR, hswap]
  have : ∫ t in Ioc a b, g t ∂F.measure = ∫ t, g t ∂μ := by rw [hμ]
  rw [this]
  linarith

end Sofa
