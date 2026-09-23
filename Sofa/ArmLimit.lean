/-
# Sofa/ArmLimit.lean — Baek Lemma 6.4.2: `∫ |g⁺_{K_n} − g⁺_K| → 0`

Baek proves Lemma 6.4.2 by the Portmanteau theorem: `g⁺_K(t) = ∫ s dσ_K` for an upper
semicontinuous `s` (Lemma 6.2.4), so weak convergence `σ_{K_n} → σ_K` gives
`limsup g⁺_{K_n}(t) ≤ g⁺_K(t)`, and the mirror argument with `g⁻` gives the reverse.

We do not need Portmanteau at all.  Theorem 6.2.5's algebraic form
`g⁺_K(t) = h_K(t) + ⟪v⁺_K(t+π/2), v_{t+π/2}⟫` reduces the statement to two facts already proved
in `Sofa/SigmaLimit.lean`: `h_{K_n} → h_K` uniformly (Hausdorff), and `v⁺_{K_n}(s) → v⁺_K(s)`
whenever `|e_K(s)| = 0` (Thm 2.1.3 + Hausdorff).  The exceptional set is countable because
`arcFn K` is monotone and its jump at `t` is exactly `|e_K(t)|`.

Contents:

* `edgeMax_sub_edgeMin`, `tendsto_arcFn_nhdsLT` — the jump of `arcFn K` at `t` is `|e_K(t)|`;
* `countable_edgeLength_ne_zero` — `σ_K` has countably many atoms (via
  `Monotone.countable_not_continuousAt`);
* `abs_edgeMax_le`, `abs_armGp_le` — the uniform bounds `≤ R`, `≤ 2R`;
* `tendsto_supportFn_of_tendsto_hausdorffDist`, **`tendsto_armGp_of_tendsto_hausdorffDist`**;
* **`tendsto_integral_k0_armGp`** — Lemma 6.4.2 in the form Equation (6.6) uses it.

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.GapArm
import Sofa.SigmaLimit

noncomputable section

open Real Set Filter Topology MeasureTheory Metric
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²}

/-! ## Uniform bounds -/

lemma abs_armGp_le {R : ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (hR : ∀ p ∈ K, ‖p‖ ≤ R) (t : ℝ) : |armGp K t| ≤ 2 * R := by
  rw [armGp_eq_add]
  refine (abs_add_le _ _).trans ?_
  linarith [abs_supportFn_le hK hne hR t, abs_edgeMax_le hK hne hR (t + π / 2)]

lemma k0_le_one_add_abs (x : ℝ) : k0 x ≤ 1 + |x| := by
  have h := k0_le_add_abs x 0
  rw [k0_of_le_one le_rfl zero_le_one, sub_zero] at h
  linarith

/-! ## Lemma 6.4.2 -/

theorem tendsto_supportFn_of_tendsto_hausdorffDist {ι : Type*} {l : Filter ι} {Ks : ι → Set ℝ²}
    (hKs : ∀ i, IsCompact (Ks i)) (hKsne : ∀ i, (Ks i).Nonempty) (hK : IsCompact K)
    (hne : K.Nonempty) (hlim : Tendsto (fun i => hausdorffDist (Ks i) K) l (𝓝 0)) (t : ℝ) :
    Tendsto (fun i => supportFn (Ks i) t) l (𝓝 (supportFn K t)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(tendsto_order.1 hlim).2 ε hε] with i hi
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (abs_supportFn_sub_le_hausdorffDist (hKs i) hK (hKsne i) hne t) hi

/-- **Baek Lemma 6.4.2** (pointwise form): `g⁺_{K_i}(t) → g⁺_K(t)` at every `t` with
`|e_K(t + π/2)| = 0`, i.e. at all but countably many `t`. -/
theorem tendsto_armGp_of_tendsto_hausdorffDist {ι : Type*} {l : Filter ι} {Ks : ι → Set ℝ²}
    (hKs : ∀ i, IsCompact (Ks i)) (hKsne : ∀ i, (Ks i).Nonempty) (hK : IsCompact K)
    (hne : K.Nonempty) (hlim : Tendsto (fun i => hausdorffDist (Ks i) K) l (𝓝 0)) {t : ℝ}
    (hdeg : edgeLength K (t + π / 2) = 0) :
    Tendsto (fun i => armGp (Ks i) t) l (𝓝 (armGp K t)) := by
  have h1 := tendsto_supportFn_of_tendsto_hausdorffDist hKs hKsne hK hne hlim t
  have h2 := tendsto_edgeMax_of_tendsto_hausdorffDist hKs hKsne hK hne hlim hdeg
  have h := h1.add h2
  simp only [← armGp_eq_add] at h
  exact h

/-- A Hausdorff-convergent sequence of compact sets is *eventually* contained in one ball. -/
theorem exists_eventually_norm_le {Ks : ℕ → Set ℝ²}
    (hKs : ∀ n, IsCompact (Ks n)) (hKsne : ∀ n, (Ks n).Nonempty) (hK : IsCompact K)
    (hne : K.Nonempty) (hlim : Tendsto (fun n => hausdorffDist (Ks n) K) atTop (𝓝 0)) :
    ∃ R : ℝ, ∀ᶠ n in atTop, ∀ p ∈ Ks n, ‖p‖ ≤ R := by
  obtain ⟨R₀, hR₀⟩ := isBounded_iff_forall_norm_le.1 hK.isBounded
  refine ⟨R₀ + 1, ?_⟩
  filter_upwards [(tendsto_order.1 hlim).2 1 one_pos] with n hn p hp
  have hfin : hausdorffEDist (Ks n) K ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (hKsne n) hne (hKs n).isBounded hK.isBounded
  obtain ⟨q, hq, hdq⟩ := hK.exists_infDist_eq_dist hne p
  have h1 : infDist p K ≤ hausdorffDist (Ks n) K := infDist_le_hausdorffDist_of_mem hp hfin
  have h2 : ‖p‖ ≤ ‖q‖ + dist p q := by
    rw [dist_eq_norm]
    have he : p = q + (p - q) := by abel
    calc ‖p‖ = ‖q + (p - q)‖ := by rw [← he]
      _ ≤ ‖q‖ + ‖p - q‖ := norm_add_le _ _
  rw [← hdq] at h2
  linarith [hR₀ q hq]

/-- **Baek Lemma 6.4.2** (the form Equation (6.6) uses): `∫_a^b k₀(g⁺_{K_n}) → ∫_a^b k₀(g⁺_K)`. -/
theorem tendsto_integral_k0_armGp {Ks : ℕ → Set ℝ²}
    (hKs : ∀ n, IsCompact (Ks n)) (hKsne : ∀ n, (Ks n).Nonempty) (hK : IsCompact K)
    (hne : K.Nonempty) (hlim : Tendsto (fun n => hausdorffDist (Ks n) K) atTop (𝓝 0))
    {R : ℝ} (hRs : ∀ᶠ n in atTop, ∀ p ∈ Ks n, ‖p‖ ≤ R) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n => ∫ t in a..b, k0 (armGp (Ks n) t)) atTop
      (𝓝 (∫ t in a..b, k0 (armGp K t))) := by
  have hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (fun t => k0 (armGp (Ks n) t))
      (volume.restrict (Ioc a b)) :=
    Eventually.of_forall fun n => (intervalIntegrable_k0_comp
      (intervalIntegrable_armGp (hKs n) (hKsne n) a b)).1.aestronglyMeasurable
  have hbdint : Integrable (fun _ : ℝ => 1 + 2 * R) (volume.restrict (Ioc a b)) :=
    integrable_const _
  have hbound : ∀ᶠ n in atTop, ∀ᵐ t ∂(volume.restrict (Ioc a b)),
      ‖k0 (armGp (Ks n) t)‖ ≤ 1 + 2 * R := by
    filter_upwards [hRs] with n hRn
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (k0_nonneg _)]
    exact (k0_le_one_add_abs _).trans
      (by linarith [abs_armGp_le (hKs n) (hKsne n) hRn t])
  have hcount : ((fun t : ℝ => t + π / 2) ⁻¹' {s : ℝ | edgeLength K s ≠ 0}).Countable :=
    (countable_edgeLength_ne_zero hK hne).preimage (add_left_injective (π / 2))
  have hlimae : ∀ᵐ t ∂(volume.restrict (Ioc a b)),
      Tendsto (fun n => k0 (armGp (Ks n) t)) atTop (𝓝 (k0 (armGp K t))) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [hcount.ae_notMem (volume : Measure ℝ)] with t ht
    have hdeg : edgeLength K (t + π / 2) = 0 := by
      by_contra hc
      exact ht (by simpa using hc)
    exact (continuous_k0.tendsto _).comp
      (tendsto_armGp_of_tendsto_hausdorffDist hKs hKsne hK hne hlim hdeg)
  have hmain := tendsto_integral_filter_of_dominated_convergence
    (F := fun n t => k0 (armGp (Ks n) t)) (f := fun t => k0 (armGp K t))
    (bound := fun _ : ℝ => 1 + 2 * R) hmeas hbound hbdint hlimae
  simp only [intervalIntegral.integral_of_le hab]
  exact hmain

end Sofa
