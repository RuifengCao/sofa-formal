/-
# Sofa/GerverTailDeriv.lean — one-sided derivatives of the tails of Gerver's niche

Baek's Thm 8.4.1 (4) for the explicit tails `B = p₁ u + p₁' v`, `D = −p₂' u + p₂ v`
(`Sofa/GerverRomik.lean`), also at the break points: for `t ∈ [π/2 − θ, π/2)` the right derivative
of `B` is `(r(π/2 − t) − 1) v_t` with `r(π/2 − t) − 1 < 0` (`r` is continuous from the left), and for
`t ∈ [0, θ)` the right derivative of `D` is `(1 − r⁺(t)) u_t` with `r⁺(t) < 1` the right limit of
`r` (`r⁺(φ) = (1 + A)/2 ≠ r(φ)`).  The proofs use `hasDerivWithinAt_Ici_of_tendsto_deriv`.

STATUS: [PROOF-C] round 39 (2026-09-23, Opus 5.5).
-/
import Sofa.GerverRomik

noncomputable section

open Real Set MovingSofa Filter Topology
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa.GP

open GC IA
open MovingSofa.GerversSofa (A B φ θ r)

/-- `r` is continuous from the left inside `(0, π/2 − φ]`. -/
lemma continuousWithinAt_r_Iic {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ π / 2 - φ) :
    ContinuousWithinAt r (Iic b) b := by
  have key : ∀ k, k ≤ 3 → b ∈ Ioc (brk k) (brk (k + 1)) → ContinuousWithinAt r (Iic b) b := by
    intro k hk hb
    have hev : r =ᶠ[𝓝[≤] b] fun s => ra k + rb k * s + rc k * s ^ 2 := by
      filter_upwards [Ioc_mem_nhdsLE hb.1] with s hs
      exact r_eq_quad hk ⟨hs.1, hs.2.trans hb.2⟩
    exact ((by fun_prop : Continuous fun s => ra k + rb k * s + rc k * s ^ 2).continuousWithinAt
      ).congr_of_eventuallyEq hev (hev.eq_of_nhdsWithin (mem_Iic.2 le_rfl))
  by_cases h1 : b ≤ brk 1
  · exact key 0 (by norm_num) ⟨hb0, h1⟩
  by_cases h2 : b ≤ brk 2
  · exact key 1 (by norm_num) ⟨not_le.1 h1, h2⟩
  by_cases h3 : b ≤ brk 3
  · exact key 2 (by norm_num) ⟨not_le.1 h2, h3⟩
  · exact key 3 (by norm_num) ⟨not_le.1 h3, hb1⟩

/-- The right limit of `r` on `[0, θ)`. -/
def rR (t : ℝ) : ℝ := if t < φ then 1 / 2 else (1 + A + t - φ) / 2

/-- `r → r⁺(t)` from the right, `t ∈ [0, θ)`. -/
lemma tendsto_r_right {t : ℝ} (ht1 : t < θ) :
    Tendsto r (𝓝[>] t) (𝓝 (rR t)) := by
  by_cases h : t < φ
  · have hev : r =ᶠ[𝓝[>] t] fun _ => (1 : ℝ) / 2 := by
      filter_upwards [Ioo_mem_nhdsGT h] with s hs
      exact r_of_le_φ hs.2.le
    rw [rR, if_pos h]
    exact (tendsto_congr' hev).2 tendsto_const_nhds
  · push Not at h
    have hev : r =ᶠ[𝓝[>] t] fun s => (1 + A + s - φ) / 2 := by
      filter_upwards [Ioo_mem_nhdsGT ht1] with s hs
      rw [r_def, if_neg (by linarith [hs.1]), if_pos hs.2.le]
    rw [rR, if_neg (not_lt.2 h)]
    refine (tendsto_congr' hev).2 ?_
    exact ((by fun_prop : Continuous fun s : ℝ => (1 + A + s - φ) / 2).tendsto t).mono_left
      nhdsWithin_le_nhds

lemma rR_lt_one {t : ℝ} (ht1 : t < θ) : rR t < 1 := by
  obtain ⟨p1, p2, t1, t2, a1, a2, -⟩ := bounds
  unfold rR
  split_ifs <;> linarith

/-- **Thm 8.4.1 (4) for `B`**: `B'(t⁺) = (r(π/2 − t) − 1) v_t` with `r(π/2 − t) − 1 < 0`,
`t ∈ [π/2 − θ, π/2)`. -/
theorem Bg_deriv : ∃ β : ℝ → ℝ, ∀ t ∈ Ico (π / 2 - θ) (π / 2),
    β t < 0 ∧ HasDerivWithinAt Bg (β t • v t) (Ici t) t := by
  obtain ⟨p1, p2, t1, t2, a1, a2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  refine ⟨fun t => r (π / 2 - t) - 1, fun t ht => ⟨?_, ?_⟩⟩
  · -- `r < 1` on `(0, θ]`
    have hs1 : π / 2 - t ≤ θ := by linarith [ht.1]
    show r (π / 2 - t) - 1 < 0
    rw [r_def]
    split_ifs <;> linarith
  · -- the next break point to the right of `t`
    obtain ⟨c, htc, hgood⟩ : ∃ c, t < c ∧ Ioo t c ⊆ good := by
      rcases lt_or_ge t (π / 2 - φ) with h | h
      · refine ⟨π / 2 - φ, h, fun s hs => mem_good.2 ⟨⟨by linarith [hs.1, ht.1], by linarith [hs.2]⟩,
          ?_, ?_, ?_, ?_⟩⟩ <;> intro he <;> linarith [hs.1, hs.2, ht.1]
      · refine ⟨π / 2, ht.2, fun s hs => mem_good.2 ⟨⟨by linarith [hs.1, ht.1], hs.2⟩,
          ?_, ?_, ?_, ?_⟩⟩ <;> intro he <;> linarith [hs.1, hs.2, h]
    refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo t c)
      (fun s hs => (hasDerivAt_Bg (continuousAt_r_of_good (good_reflect (hgood hs)))
        ).differentiableAt.differentiableWithinAt)
      continuous_Bg.continuousWithinAt (Ioo_mem_nhdsGT htc) ?_
    have hr : Tendsto (fun s => r (π / 2 - s)) (𝓝[>] t) (𝓝 (r (π / 2 - t))) := by
      have hc := continuousWithinAt_r_Iic (b := π / 2 - t) (by linarith [ht.2])
        (by linarith [ht.1])
      refine hc.tendsto.comp ?_
      refine ((continuous_sub_left (π / 2)).continuousWithinAt.tendsto_nhdsWithin ?_)
      intro s hs
      simp only [mem_Ioi] at hs
      simp only [mem_Iic]
      linarith
    have hlim : Tendsto (fun s => (r (π / 2 - s) - 1) • v s) (𝓝[>] t)
        (𝓝 ((r (π / 2 - t) - 1) • v t)) :=
      (hr.sub_const 1).smul ((continuous_v.tendsto t).mono_left nhdsWithin_le_nhds)
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT htc] with s hs
    exact ((hasDerivAt_Bg (continuousAt_r_of_good (good_reflect (hgood hs)))).deriv).symm

/-- **Thm 8.4.1 (4) for `D`**: `D'(t⁺) = (1 − r⁺(t)) u_t` with `1 − r⁺(t) > 0`, `t ∈ [0, θ)`. -/
theorem Dg_deriv : ∃ δ : ℝ → ℝ, ∀ t ∈ Ico 0 θ,
    0 < δ t ∧ HasDerivWithinAt Dg (δ t • u t) (Ici t) t := by
  obtain ⟨p1, p2, t1, t2, a1, a2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  refine ⟨fun t => 1 - rR t, fun t ht => ⟨by linarith [rR_lt_one ht.2], ?_⟩⟩
  obtain ⟨c, htc, hgood⟩ : ∃ c, t < c ∧ Ioo t c ⊆ good := by
    rcases lt_or_ge t φ with h | h
    · refine ⟨φ, h, fun s hs => mem_good.2 ⟨⟨by linarith [hs.1, ht.1], by linarith [hs.2]⟩,
        ?_, ?_, ?_, ?_⟩⟩ <;> intro he <;> linarith [hs.1, hs.2, ht.1]
    · refine ⟨θ, ht.2, fun s hs => mem_good.2 ⟨⟨by linarith [hs.1, ht.1], by linarith [hs.2]⟩,
        ?_, ?_, ?_, ?_⟩⟩ <;> intro he <;> linarith [hs.1, hs.2, h]
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo t c)
    (fun s hs => (hasDerivAt_Dg (continuousAt_r_of_good (hgood hs))
      ).differentiableAt.differentiableWithinAt)
    continuous_Dg.continuousWithinAt (Ioo_mem_nhdsGT htc) ?_
  have hlim : Tendsto (fun s => (1 - r s) • u s) (𝓝[>] t) (𝓝 ((1 - rR t) • u t)) :=
    ((tendsto_r_right ht.2).const_sub 1).smul
      ((continuous_u.tendsto t).mono_left nhdsWithin_le_nhds)
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT htc] with s hs
  exact ((hasDerivAt_Dg (continuousAt_r_of_good (hgood hs))).deriv).symm

end Sofa.GP
