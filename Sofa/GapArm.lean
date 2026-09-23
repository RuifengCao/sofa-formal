/-
# Sofa/GapArm.lean — Baek Lemma 6.4.1: `g⁺_K` is Lipschitz on a gap between normals

Baek's Lemma 6.4.1 says that for a maximum polygon cap `K` with step size `δ` and two adjacent
angles `t, t + δ`, the arm length `g⁺_K` varies by at most `5δ` on `[t, t + δ)`.  His proof is a
Thales-circle argument (the outer corner `y_K(t')` runs along an arc of a circle through
`A = A⁺_K(t)` and `C = C⁺_K(t)`) and needs Lemma 6.3.1 (`diam K ≤ 5`).

We replace both by a two-line computation.  On the gap the vertex map is *constant*
(`vtxP_const_on_gap`, `Sofa/NicheBound.lean`), say `v⁺_K ≡ C` on `[a, b)`, so Theorem 6.2.5's
algebraic form `g⁺_K(s) = h_K(s) + ⟪v⁺_K(s + π/2), v_{s+π/2}⟫` becomes

    `g⁺_K(s) = h_K(s) − ⟪C, u_s⟫`   for `s + π/2 ∈ [a, b)`,

a difference of two `R`-Lipschitz functions of `s` (`h_K` by `Sofa/SupportLipschitz.lean`, and
`s ↦ ⟪C, u_s⟫` because `‖C‖ ≤ R` and `‖u_s − u_{s'}‖ ≤ |s − s'|`).  Hence `g⁺_K` is `2R`-Lipschitz
there.  The constant `2R` is uniform along a Hausdorff-convergent sequence of caps, which is all
Theorem 6.4.3 needs — **Lemma 6.3.1 is not used**.

Contents:

* `k0_eq_abs`, `abs_k0_sub_le` — `k₀` written with absolute values, and its 1-Lipschitz bound;
* `intervalIntegrable_armGp`, `intervalIntegrable_k0_comp` — integrability of `k₀ ∘ g⁺_K`;
* `vtxP_const_on_Ico_gap` — the vertex map is constant on `[a, b)` when `(a, b)` avoids normals
  (one-sided extension of `vtxP_const_on_gap`, by right-continuity of `v⁺_K`);
* `armGp_eq_sub_inner`, `abs_armGp_sub_le_gap` — **Lemma 6.4.1**;
* `abs_integral_k0_armGp_sub_le` — its integrated form, the input to Equation (6.4).

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.NicheBound

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

/-! ## `k₀` is 1-Lipschitz -/

/-- `k₀(x) = (3|x − 1| + 1 + ||x − 1| − 1|)/4`, using `max a b = (a + b + |a − b|)/2`. -/
lemma k0_eq_abs (x : ℝ) : k0 x = (3 * |x - 1| + 1 + |(|x - 1| - 1)|) / 4 := by
  rw [k0]
  rcases le_or_gt |x - 1| 1 with h | h
  · rw [max_eq_right (by linarith), abs_of_nonpos (show |x - 1| - 1 ≤ 0 by linarith)]
    ring
  · rw [max_eq_left (by linarith), abs_of_nonneg (show (0:ℝ) ≤ |x - 1| - 1 by linarith)]
    ring

lemma k0_le_add_abs (x y : ℝ) : k0 x ≤ k0 y + |x - y| := by
  have habs : |x - 1| ≤ |y - 1| + |x - y| := by
    have h := abs_sub_abs_le_abs_sub (x - 1) (y - 1)
    rw [show x - 1 - (y - 1) = x - y by ring] at h
    linarith
  have h1 := abs_le_k0 y
  have h2 := half_le_k0 y
  have h3 := abs_nonneg (x - y)
  rw [k0]
  exact max_le (by linarith) (by linarith)

/-- **`k₀` is 1-Lipschitz.** -/
lemma abs_k0_sub_le (x y : ℝ) : |k0 x - k0 y| ≤ |x - y| := by
  rw [abs_sub_le_iff]
  refine ⟨by linarith [k0_le_add_abs x y], ?_⟩
  have h := k0_le_add_abs y x
  rw [abs_sub_comm y x] at h
  linarith

lemma lipschitzWith_k0 : LipschitzWith 1 k0 := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
  exact abs_k0_sub_le x y

/-! ## Integrability of `k₀ ∘ g⁺_K` -/

variable {K : Set ℝ²}

lemma intervalIntegrable_armGp (hK : IsCompact K) (hne : K.Nonempty) (a b : ℝ) :
    IntervalIntegrable (armGp K) volume a b := by
  have he : armGp K = fun t => supportFn K t + edgeMax K (t + π / 2) := funext (armGp_eq_add K)
  rw [he]
  refine (integrable_supportFn hK hne a b).add ?_
  have h := (intervalIntegrable_edgeMax hK hne (a + π / 2) (b + π / 2)).comp_add_right (π / 2)
  rwa [add_sub_cancel_right, add_sub_cancel_right] at h

lemma intervalIntegrable_k0_comp {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun r => k0 (f r)) volume a b := by
  have h1 : IntervalIntegrable (fun r => |f r - 1|) volume a b :=
    (hf.sub (intervalIntegrable_const (μ := volume) (c := (1:ℝ)))).abs
  have h2 : IntervalIntegrable (fun r => |(|f r - 1| - 1)|) volume a b :=
    (h1.sub (intervalIntegrable_const (μ := volume) (c := (1:ℝ)))).abs
  have he : (fun r => k0 (f r))
      = fun r => (3 * |f r - 1| + 1 + |(|f r - 1| - 1)|) / 4 := funext fun r => k0_eq_abs (f r)
  rw [he]
  exact (((h1.const_mul 3).add
    (intervalIntegrable_const (μ := volume) (c := (1:ℝ)))).add h2).div_const 4

/-! ## The vertex map on a half-open gap -/

section Gap

variable (hKc : IsCompact K) (hKne : K.Nonempty) (hconv : Convex ℝ K)
  {A : Finset ℝ} (hA : K = ⋂ r ∈ A, hpLe r (supportFn K r))
  (hwidth : ∀ s, 0 < supportFn K s + supportFn K (s + π))
  {a b : ℝ} (hgap : ∀ t ∈ Ioo a b, ∀ r ∈ A, u r ≠ u t)

include hKc hKne hconv hA hwidth hgap

/-- **`v⁺_K` is constant on `[a, b)`** when the *open* interval `(a, b)` contains no normal
direction.  (The endpoint `a` is allowed to be a normal: `v⁺_K` is right-continuous there, and
`v⁺_K(a)` is exactly the far endpoint of the edge at `a`, i.e. the constant value on the gap.) -/
theorem vtxP_const_on_Ico_gap : ∀ t ∈ Ico a b, vtxP K t = vtxP K a := by
  have hIoo : ∀ t ∈ Ioo a b, vtxP K t = vtxP K a := by
    intro t ht
    have hconst : ∀ s ∈ Ioo a t, vtxP K t = vtxP K s := by
      intro s hs
      have hsub : ∀ y ∈ Icc s t, ∀ r ∈ A, u r ≠ u y := fun y hy r hr =>
        hgap y ⟨lt_of_lt_of_le hs.1 hy.1, lt_of_le_of_lt hy.2 ht.2⟩ r hr
      exact vtxP_const_on_gap hKc hKne hconv hA hwidth hsub t ⟨hs.2.le, le_rfl⟩
    have h1 : Tendsto (vtxP K) (𝓝[>] a) (𝓝 (vtxP K a)) :=
      (continuousWithinAt_vtxP hKc hKne a).mono_left (nhdsWithin_mono a Ioi_subset_Ici_self)
    have h2 : Tendsto (vtxP K) (𝓝[>] a) (𝓝 (vtxP K t)) := by
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
      exact hconst s hs
    exact (tendsto_nhds_unique h1 h2).symm
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h]
  · exact hIoo t ⟨h, ht.2⟩

/-- **`arcFn K` is constant on `[a, b)`**, i.e. `σ_K` puts no mass on the gap. -/
theorem arcFn_const_on_Ico_gap : ∀ t ∈ Ico a b, arcFn K t = arcFn K a := by
  intro t ht
  have hQ := vtxP_const_on_Ico_gap hKc hKne hconv hA hwidth hgap
  have hat : a ≤ t := ht.1
  have hint : (∫ s in (0:ℝ)..t, supportFn K s) - ∫ s in (0:ℝ)..a, supportFn K s
      = ∫ s in a..t, supportFn K s :=
    intervalIntegral.integral_interval_sub_left (integrable_supportFn hKc hKne 0 t)
      (integrable_supportFn hKc hKne 0 a)
  have heq : (∫ s in a..t, supportFn K s) = ⟪vtxP K a, v a⟫ - ⟪vtxP K a, v t⟫ := by
    rw [← integral_inner_u (vtxP K a) a t]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hat] at hs
    rw [← hQ s ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩, inner_vtxP_u]
  rw [arcFn, arcFn, hQ t ht]
  linarith [hint, heq]

/-- On the gap, Theorem 6.2.5's algebraic form collapses to `g⁺_K(s) = h_K(s) − ⟪C, u_s⟫`. -/
theorem armGp_eq_sub_inner {s : ℝ} (hs : s + π / 2 ∈ Ico a b) :
    armGp K s = supportFn K s - ⟪vtxP K a, u s⟫ := by
  rw [armGp_eq_add, ← inner_vtxP_v,
    vtxP_const_on_Ico_gap hKc hKne hconv hA hwidth hgap (s + π / 2) hs,
    v_add_pi_div_two, inner_neg_right]
  ring

/-- **Baek Lemma 6.4.1.**  On a gap between normals, `g⁺_K` is `2R`-Lipschitz. -/
theorem abs_armGp_sub_le_gap {R : ℝ} (hR : ∀ p ∈ K, ‖p‖ ≤ R) {s s' : ℝ}
    (hs : s + π / 2 ∈ Ico a b) (hs' : s' + π / 2 ∈ Ico a b) :
    |armGp K s' - armGp K s| ≤ 2 * R * |s' - s| := by
  have hCK : vtxP K a ∈ K := vtxP_mem hKc hKne a
  have hC : ‖vtxP K a‖ ≤ R := hR _ hCK
  have hC0 : (0:ℝ) ≤ ‖vtxP K a‖ := norm_nonneg _
  have hR0 : (0:ℝ) ≤ R := le_trans hC0 hC
  have h1 : |supportFn K s' - supportFn K s| ≤ R * |s' - s| :=
    abs_supportFn_sub_le hKc hKne hR s' s
  have h2 : |⟪vtxP K a, u s'⟫ - ⟪vtxP K a, u s⟫| ≤ R * |s' - s| := by
    rw [← inner_sub_right]
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    exact mul_le_mul hC (norm_u_sub_u_le s' s) (norm_nonneg _) hR0
  rw [armGp_eq_sub_inner hKc hKne hconv hA hwidth hgap hs,
    armGp_eq_sub_inner hKc hKne hconv hA hwidth hgap hs']
  obtain ⟨h1a, h1b⟩ := abs_le.1 h1
  obtain ⟨h2a, h2b⟩ := abs_le.1 h2
  rw [abs_le]
  constructor <;> linarith

/-- **Lemma 6.4.1, integrated form** — this is what Equation (6.4) uses:

    `|∫_t^{t+δ} k₀(g⁺_K(r)) dr − k₀(g⁺_K(t))·δ| ≤ 2R δ²`. -/
theorem abs_integral_k0_armGp_sub_le {R : ℝ} (hR : ∀ p ∈ K, ‖p‖ ≤ R) {t δ : ℝ} (hδ : 0 ≤ δ)
    (ht : t + π / 2 ∈ Ico a b) (ht' : t + δ + π / 2 ≤ b) :
    |(∫ r in t..(t + δ), k0 (armGp K r)) - k0 (armGp K t) * δ| ≤ 2 * R * δ ^ 2 := by
  have hR0 : (0:ℝ) ≤ R := le_trans (norm_nonneg _) (hR _ (vtxP_mem hKc hKne a))
  have hint : IntervalIntegrable (fun r => k0 (armGp K r)) volume t (t + δ) :=
    intervalIntegrable_k0_comp (intervalIntegrable_armGp hKc hKne t (t + δ))
  have hconst : IntervalIntegrable (fun _ : ℝ => k0 (armGp K t)) volume t (t + δ) :=
    intervalIntegrable_const (μ := volume) (c := k0 (armGp K t))
  have hsplit : (∫ r in t..(t + δ), (k0 (armGp K r) - k0 (armGp K t)))
      = (∫ r in t..(t + δ), k0 (armGp K r)) - k0 (armGp K t) * δ := by
    rw [intervalIntegral.integral_sub hint hconst, intervalIntegral.integral_const,
      smul_eq_mul]
    ring_nf
  have hbound : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Set.uIoc t (t + δ) →
      ‖k0 (armGp K r) - k0 (armGp K t)‖ ≤ 2 * R * δ := by
    filter_upwards [(Set.countable_singleton (t + δ)).ae_notMem (volume : Measure ℝ)]
      with r hrne hr
    rw [Set.uIoc_of_le (by linarith : t ≤ t + δ)] at hr
    have hrlt : r < t + δ := lt_of_le_of_ne hr.2 (by simpa using hrne)
    have hrmem : r + π / 2 ∈ Ico a b :=
      ⟨le_trans ht.1 (by linarith [hr.1]), by linarith⟩
    have hle : |r - t| ≤ δ := by
      rw [abs_of_nonneg (by linarith [hr.1] : (0:ℝ) ≤ r - t)]; linarith [hr.2]
    calc ‖k0 (armGp K r) - k0 (armGp K t)‖
        = |k0 (armGp K r) - k0 (armGp K t)| := Real.norm_eq_abs _
      _ ≤ |armGp K r - armGp K t| := abs_k0_sub_le _ _
      _ ≤ 2 * R * |r - t| :=
            abs_armGp_sub_le_gap hKc hKne hconv hA hwidth hgap hR ht hrmem
      _ ≤ 2 * R * δ := by
            have : (0:ℝ) ≤ 2 * R := by linarith
            exact mul_le_mul_of_nonneg_left hle this
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const_ae hbound
  rw [hsplit, Real.norm_eq_abs, show t + δ - t = δ by ring, abs_of_nonneg hδ] at hmain
  calc |(∫ r in t..(t + δ), k0 (armGp K r)) - k0 (armGp K t) * δ|
      ≤ 2 * R * δ * δ := hmain
    _ = 2 * R * δ ^ 2 := by ring

/-- The direction Equation (6.4) uses:
`k₀(g⁺_K(t))·δ ≤ ∫_t^{t+δ} k₀(g⁺_K(r)) dr + 2R δ²`. -/
theorem k0_armGp_mul_le_integral {R : ℝ} (hR : ∀ p ∈ K, ‖p‖ ≤ R) {t δ : ℝ} (hδ : 0 ≤ δ)
    (ht : t + π / 2 ∈ Ico a b) (ht' : t + δ + π / 2 ≤ b) :
    k0 (armGp K t) * δ ≤ (∫ r in t..(t + δ), k0 (armGp K r)) + 2 * R * δ ^ 2 := by
  have h := abs_le.1 (abs_integral_k0_armGp_sub_le hKc hKne hconv hA hwidth hgap hR hδ ht ht')
  linarith [h.1]

end Gap

end Sofa
