/-
# Sofa/GapSum.lean — Baek Equation (6.5): summing the step inequality

Theorem 6.4.3 sums the one-step bound of Theorem 6.3.3 / Lemma 6.4.1

    `σ_K((t, t+δ]) ≤ ∫_{t+δ}^{t+2δ} k₀(g⁺_K(s)) ds + E`   (`E = O(δ²)`)

over the `N` steps of a uniform partition and telescopes the integrals.  Both ingredients are
completely independent of the polygon structure, so they are isolated here:

* `measure_Ioc_le_sum` — finite subadditivity along a monotone sequence of cut points;
* `sigmaK_Ioc_le_integral_of_steps` — **Equation (6.5)**;
* `integral_k0_armGp_shift_le` — replacing `∫_{a+δ}^{b+δ}` by `∫_a^b` costs at most `(1+2R)δ`,
  which turns Equation (6.5) into the form Theorem 6.4.3 uses:

    `σ_K((a, b]) ≤ ∫_a^b k₀(g⁺_K) + N·E + (1 + 2R)·δ`.

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.ArmLimit

noncomputable section

open Real Set Filter Topology MeasureTheory Metric
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

/-! ## Finite subadditivity along a monotone sequence of cut points -/

theorem measure_Ioc_le_sum {μ : Measure ℝ} {f : ℕ → ℝ} (hmono : Monotone f) {c : ℕ → ℝ}
    (hc : ∀ j, 0 ≤ c j) :
    ∀ N : ℕ, (∀ j < N, μ (Ioc (f j) (f (j + 1))) ≤ ENNReal.ofReal (c j)) →
      μ (Ioc (f 0) (f N)) ≤ ENNReal.ofReal (∑ j ∈ Finset.range N, c j) := by
  intro N
  induction N with
  | zero => intro _; simp
  | succ n ih =>
      intro hstep
      have h1 : μ (Ioc (f 0) (f n)) ≤ ENNReal.ofReal (∑ j ∈ Finset.range n, c j) :=
        ih fun j hj => hstep j (by omega)
      have h2 := hstep n (by omega)
      have hunion : Ioc (f 0) (f n) ∪ Ioc (f n) (f (n + 1)) = Ioc (f 0) (f (n + 1)) :=
        Ioc_union_Ioc_eq_Ioc (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n))
      have hsum0 : (0:ℝ) ≤ ∑ j ∈ Finset.range n, c j :=
        Finset.sum_nonneg fun j _ => hc j
      calc μ (Ioc (f 0) (f (n + 1))) = μ (Ioc (f 0) (f n) ∪ Ioc (f n) (f (n + 1))) := by
            rw [hunion]
        _ ≤ μ (Ioc (f 0) (f n)) + μ (Ioc (f n) (f (n + 1))) := measure_union_le _ _
        _ ≤ ENNReal.ofReal (∑ j ∈ Finset.range n, c j) + ENNReal.ofReal (c n) :=
            add_le_add h1 h2
        _ = ENNReal.ofReal (∑ j ∈ Finset.range (n + 1), c j) := by
            rw [Finset.sum_range_succ, ENNReal.ofReal_add hsum0 (hc n)]

/-! ## Equation (6.5) -/

variable {K : Set ℝ²}

/-- **Baek Equation (6.5).**  If each step of a uniform partition satisfies the one-step bound,
the total surface measure is bounded by the shifted integral plus `N·E`. -/
theorem sigmaK_Ioc_le_integral_of_steps (hKc : IsCompact K) (hKne : K.Nonempty)
    {a δ : ℝ} (hδ : 0 ≤ δ) (N : ℕ) {E : ℝ} (hE : 0 ≤ E)
    (hstep : ∀ j < N, (sigmaK K (Ioc (a + j * δ) (a + (j + 1) * δ))).toReal
        ≤ (∫ t in (a + (j + 1) * δ)..(a + (j + 2) * δ), k0 (armGp K t)) + E) :
    (sigmaK K (Ioc a (a + N * δ))).toReal
      ≤ (∫ t in (a + δ)..(a + (N + 1) * δ), k0 (armGp K t)) + N * E := by
  set f : ℕ → ℝ := fun j => a + j * δ with hf
  set g : ℕ → ℝ := fun j => a + (j + 1) * δ with hg
  set c : ℕ → ℝ := fun j => (∫ t in (g j)..(g (j + 1)), k0 (armGp K t)) + E with hcdef
  have hgle : ∀ j : ℕ, g j ≤ g (j + 1) := by
    intro j; simp only [hg]; push_cast; nlinarith
  have hint : ∀ j : ℕ, IntervalIntegrable (fun t => k0 (armGp K t)) volume (g j) (g (j + 1)) :=
    fun j => intervalIntegrable_k0_comp (intervalIntegrable_armGp hKc hKne _ _)
  have hc : ∀ j, 0 ≤ c j := by
    intro j
    have h := intervalIntegral.integral_nonneg (μ := volume) (hgle j)
      (fun t _ => k0_nonneg (armGp K t))
    simp only [hcdef]
    linarith
  have hmono : Monotone f := by
    intro i j hij
    simp only [hf]
    have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.2 hij
    nlinarith
  have hstep' : ∀ j < N, sigmaK K (Ioc (f j) (f (j + 1))) ≤ ENNReal.ofReal (c j) := by
    intro j hj
    have hfin : sigmaK K (Ioc (f j) (f (j + 1))) ≠ ⊤ := by
      rw [hf]
      simp only
      rw [sigmaK_Ioc hKc hKne]
      exact ENNReal.ofReal_ne_top
    have hle := hstep j hj
    have heq : f (j + 1) = a + ((j : ℝ) + 1) * δ := by simp only [hf]; push_cast; ring
    have heq0 : f j = a + (j : ℝ) * δ := by simp only [hf]
    rw [← ENNReal.ofReal_toReal hfin]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [heq, heq0]
    refine hle.trans (le_of_eq ?_)
    simp only [hcdef, hg]
    push_cast
    ring_nf
  have hmain := measure_Ioc_le_sum (μ := sigmaK K) hmono hc N hstep'
  have hfN : f N = a + (N : ℝ) * δ := by simp only [hf]
  have hf0 : f 0 = a := by simp only [hf]; push_cast; ring
  rw [hf0, hfN] at hmain
  have hsum : (∑ j ∈ Finset.range N, c j)
      = (∫ t in (g 0)..(g N), k0 (armGp K t)) + N * E := by
    simp only [hcdef]
    rw [Finset.sum_add_distrib, intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => hint k), Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hg0 : g 0 = a + δ := by simp only [hg]; push_cast; ring
  have hgN : g N = a + ((N : ℝ) + 1) * δ := by simp only [hg]
  rw [hsum, hg0, hgN] at hmain
  refine ENNReal.toReal_le_of_le_ofReal ?_ hmain
  have h := intervalIntegral.integral_nonneg (μ := volume) (a := a + δ)
    (b := a + ((N : ℝ) + 1) * δ) (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
    (fun t _ => k0_nonneg (armGp K t))
  have : (0:ℝ) ≤ (N : ℝ) * E := mul_nonneg (Nat.cast_nonneg N) hE
  linarith

/-- Shifting the integration window by `δ` costs at most `(1 + 2R)·δ`. -/
theorem integral_k0_armGp_shift_le {R : ℝ} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hR : ∀ p ∈ K, ‖p‖ ≤ R) {a b δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ t in (a + δ)..(b + δ), k0 (armGp K t))
      ≤ (∫ t in a..b, k0 (armGp K t)) + (1 + 2 * R) * δ := by
  have hbd : ∀ t : ℝ, k0 (armGp K t) ≤ 1 + 2 * R :=
    fun t => (k0_le_one_add_abs _).trans (by linarith [abs_armGp_le hKc hKne hR t])
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun t => k0 (armGp K t)) volume x y :=
    fun x y => intervalIntegrable_k0_comp (intervalIntegrable_armGp hKc hKne _ _)
  have hsplitL : (∫ t in (a + δ)..(b + δ), k0 (armGp K t))
      = (∫ t in (a + δ)..b, k0 (armGp K t)) + ∫ t in b..(b + δ), k0 (armGp K t) :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  have hsplitR : (∫ t in a..b, k0 (armGp K t))
      = (∫ t in a..(a + δ), k0 (armGp K t)) + ∫ t in (a + δ)..b, k0 (armGp K t) :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  have hlast : (∫ t in b..(b + δ), k0 (armGp K t)) ≤ (1 + 2 * R) * δ := by
    have h := intervalIntegral.integral_mono_on (by linarith : b ≤ b + δ) (hint b (b + δ))
      (intervalIntegrable_const (μ := volume) (c := 1 + 2 * R)) (fun t _ => hbd t)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    calc (∫ t in b..(b + δ), k0 (armGp K t)) ≤ (b + δ - b) * (1 + 2 * R) := h
      _ = (1 + 2 * R) * δ := by ring
  have hfirst : 0 ≤ ∫ t in a..(a + δ), k0 (armGp K t) :=
    intervalIntegral.integral_nonneg (μ := volume) (by linarith) (fun t _ => k0_nonneg _)
  linarith

/-! ## The surface measure of a step is the atom at its right endpoint -/

/-- **`σ_K((a, b]) = σ_K({b})`** when the open interval `(a, b)` contains no normal direction:
all of the mass of a step sits at its right endpoint.  This is the `Ioc`-form of Baek's
`σ_{K_n}([t, t+δ)) = σ_{K_n}({t})`. -/
theorem sigmaK_Ioc_eq_singleton_of_gap (hKc : IsCompact K) (hKne : K.Nonempty)
    (hconv : Convex ℝ K) {A : Finset ℝ} (hA : K = ⋂ r ∈ A, hpLe r (supportFn K r))
    (hwidth : ∀ s, 0 < supportFn K s + supportFn K (s + π))
    {a b : ℝ} (hab : a < b) (hgap : ∀ t ∈ Ioo a b, ∀ r ∈ A, u r ≠ u t) :
    sigmaK K (Ioc a b) = sigmaK K {b} := by
  have hconst := arcFn_const_on_Ico_gap hKc hKne hconv hA hwidth hgap
  have h1 : Tendsto (arcFn K) (𝓝[<] b) (𝓝 (arcFn K a)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsLT hab] with s hs
    exact (hconst s ⟨hs.1.le, hs.2⟩).symm
  have h2 := tendsto_arcFn_nhdsLT hKc hKne b
  have heq := tendsto_nhds_unique h1 h2
  rw [sigmaK_Ioc hKc hKne, sigmaK_singleton hKc hKne]
  congr 1
  linarith

/-! ## Theorem 6.4.3, conditionally on the discrete bound -/

/-- **Baek Theorem 6.4.3** (the limit step).  If the polygon caps `K_n → K` all satisfy the
discrete inequality `σ_{K_n}((a,b]) ≤ ∫_a^b k₀(g⁺_{K_n}) + err n` with `err n → 0`, then
`σ_K((a,b]) ≤ ∫_a^b k₀(g⁺_K)` at every pair of continuity points `a, b` of `arcFn K`.

Both limits are *genuine limits*, not `liminf`s: `σ_{K_n}((a,b]) → σ_K((a,b])` by
`tendsto_sigmaK_Ioc` (weak convergence at continuity points) and
`∫ k₀(g⁺_{K_n}) → ∫ k₀(g⁺_K)` by `tendsto_integral_k0_armGp` (Lemma 6.4.2). -/
theorem sigmaK_Ioc_le_integral_of_limit {Ks : ℕ → Set ℝ²}
    (hKs : ∀ n, IsCompact (Ks n)) (hKsne : ∀ n, (Ks n).Nonempty)
    (hKc : IsCompact K) (hKne : K.Nonempty)
    (hlim : Tendsto (fun n => hausdorffDist (Ks n) K) atTop (𝓝 0))
    {R : ℝ} (hRs : ∀ᶠ n in atTop, ∀ p ∈ Ks n, ‖p‖ ≤ R)
    {a b : ℝ} (hab : a ≤ b) (hda : edgeLength K a = 0) (hdb : edgeLength K b = 0)
    {err : ℕ → ℝ} (herr : Tendsto err atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, (sigmaK (Ks n) (Ioc a b)).toReal
        ≤ (∫ t in a..b, k0 (armGp (Ks n) t)) + err n) :
    (sigmaK K (Ioc a b)).toReal ≤ ∫ t in a..b, k0 (armGp K t) := by
  have h1 := tendsto_sigmaK_Ioc hKs hKsne hKc hKne hlim hab hda hdb
  have h2 := tendsto_integral_k0_armGp hKs hKsne hKc hKne hlim hRs hab
  have h3 := h2.add herr
  rw [add_zero] at h3
  exact le_of_tendsto_of_tendsto h1 h3 hbound

/-- The version Theorem 6.4.3 actually needs: the discrete bound is available only on the
*dyadic* interval `(a', b']` (the cut points of `Θ_n`), while the limit
`σ_{K_n}((a,b]) → σ_K((a,b])` needs `a`, `b` to be continuity points of `arcFn K`.  Monotonicity
of `σ_{K_n}` bridges the two: take `[a, b] ⊆ [a', b']`. -/
theorem sigmaK_Ioc_le_integral_of_limit' {Ks : ℕ → Set ℝ²}
    (hKs : ∀ n, IsCompact (Ks n)) (hKsne : ∀ n, (Ks n).Nonempty)
    (hKc : IsCompact K) (hKne : K.Nonempty)
    (hlim : Tendsto (fun n => hausdorffDist (Ks n) K) atTop (𝓝 0))
    {R : ℝ} (hRs : ∀ᶠ n in atTop, ∀ p ∈ Ks n, ‖p‖ ≤ R)
    {a b a' b' : ℝ} (hab : a ≤ b) (ha : a' ≤ a) (hb : b ≤ b')
    (hda : edgeLength K a = 0) (hdb : edgeLength K b = 0)
    {err : ℕ → ℝ} (herr : Tendsto err atTop (𝓝 0))
    (hbound : ∀ᶠ n in atTop, (sigmaK (Ks n) (Ioc a' b')).toReal
        ≤ (∫ t in a'..b', k0 (armGp (Ks n) t)) + err n) :
    (sigmaK K (Ioc a b)).toReal ≤ ∫ t in a'..b', k0 (armGp K t) := by
  have h1 := tendsto_sigmaK_Ioc hKs hKsne hKc hKne hlim hab hda hdb
  have h2 := tendsto_integral_k0_armGp hKs hKsne hKc hKne hlim hRs (hab.trans hb |>.trans' ha)
  have h3 := h2.add herr
  rw [add_zero] at h3
  refine le_of_tendsto_of_tendsto h1 h3 ?_
  filter_upwards [hbound] with n hn
  refine le_trans ?_ hn
  have hfin : sigmaK (Ks n) (Ioc a' b') ≠ ⊤ := by
    rw [sigmaK_Ioc (hKs n) (hKsne n)]; exact ENNReal.ofReal_ne_top
  exact ENNReal.toReal_mono hfin (measure_mono (Ioc_subset_Ioc ha hb))

/-- Shrinking the integration window back to `[a, b]` costs at most `(1 + 2R)(b − a' + b' − b)`,
so letting `a' ↑ a` and `b' ↓ b` in `sigmaK_Ioc_le_integral_of_limit'` gives
`σ_K((a,b]) ≤ ∫_a^b k₀(g⁺_K)`. -/
theorem integral_k0_armGp_widen_le {R : ℝ} (hKc : IsCompact K) (hKne : K.Nonempty)
    (hR : ∀ p ∈ K, ‖p‖ ≤ R) {a b a' b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    (∫ t in a'..b', k0 (armGp K t))
      ≤ (∫ t in a..b, k0 (armGp K t)) + (1 + 2 * R) * ((a - a') + (b' - b)) := by
  have hbd : ∀ t : ℝ, k0 (armGp K t) ≤ 1 + 2 * R :=
    fun t => (k0_le_one_add_abs _).trans (by linarith [abs_armGp_le hKc hKne hR t])
  have hR0 : (0:ℝ) ≤ R := by
    obtain ⟨p, hp⟩ := hKne
    exact le_trans (norm_nonneg p) (hR p hp)
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun t => k0 (armGp K t)) volume x y :=
    fun x y => intervalIntegrable_k0_comp (intervalIntegrable_armGp hKc hKne _ _)
  have hconstbd : ∀ x y : ℝ, x ≤ y →
      (∫ t in x..y, k0 (armGp K t)) ≤ (1 + 2 * R) * (y - x) := by
    intro x y hxy
    have h := intervalIntegral.integral_mono_on hxy (hint x y)
      (intervalIntegrable_const (μ := volume) (c := 1 + 2 * R)) (fun t _ => hbd t)
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    calc (∫ t in x..y, k0 (armGp K t)) ≤ (y - x) * (1 + 2 * R) := h
      _ = (1 + 2 * R) * (y - x) := by ring
  have h1 : (∫ t in a'..b', k0 (armGp K t))
      = (∫ t in a'..a, k0 (armGp K t)) + ∫ t in a..b', k0 (armGp K t) :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  have h2 : (∫ t in a..b', k0 (armGp K t))
      = (∫ t in a..b, k0 (armGp K t)) + ∫ t in b..b', k0 (armGp K t) :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  have h3 := hconstbd a' a ha
  have h4 := hconstbd b b' hb
  rw [h1, h2]
  linarith

end Sofa
