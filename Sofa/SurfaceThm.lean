/-
# Sofa/SurfaceThm.lean — Baek Theorem 5.2.2: `d v⁺_K(t) = v_t σ_K(dt)`

`Sofa/SurfaceArea.lean` *defines* `σ_K` as the Lebesgue–Stieltjes measure of

    `arcFn K t = ⟪v⁺_K(t), v_t⟫ + ∫_0^t h_K`,

so that `σ_K((a,b]) = ⟪v⁺_K(b), v_b⟫ − ⟪v⁺_K(a), v_a⟫ + ∫_a^b h_K` by construction.  Here we
prove the vector identity that this definition is designed to produce:

    `⟪v⁺_K(b) − v⁺_K(a), e⟫ = ∫_{(a,b]} ⟪v_t, e⟫ σ_K(dt)`   for every fixed `e ∈ ℝ²`.

The proof is a Riemann-sum estimate.  On a short interval the two-sided bounds of
`Sofa/SurfaceArea.lean` give

    `0 ≤ ⟪d, u_b⟫ ≤ tan δ · σ`,   `0 ≤ σ − ⟪d, v_b⟫ ≤ δ tan δ · σ`      (`d = v⁺(b) − v⁺(a)`),

hence `|⟪d, e⟫ − ⟪v_b, e⟫ σ| ≤ ‖e‖ (tan δ)(1 + δ) σ`, and `⟪v_t, e⟫` is `‖e‖`-Lipschitz, so the
defect over `(a,b]` is `≤ 5‖e‖ δ σ((a,b])` for `δ = b − a ≤ 1`.  Chaining over a partition of
mesh `δ` keeps the same bound, and `δ → 0` finishes.

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.SurfaceArea

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²}

/-! ## Elementary estimates -/

/-- Orthonormal expansion in the moving frame `(u_t, v_t)`. -/
lemma inner_expand (d e : ℝ²) (t : ℝ) :
    ⟪d, e⟫ = ⟪d, u t⟫ * ⟪u t, e⟫ + ⟪d, v t⟫ * ⟪v t, e⟫ := by
  simp only [inner_eq, u_coord_zero, u_coord_one, v_coord_zero, v_coord_one]
  linear_combination (-(d 0 * e 0 + d 1 * e 1)) * sin_sq_add_cos_sq t

lemma abs_inner_u_le (e : ℝ²) (t : ℝ) : |⟪u t, e⟫| ≤ ‖e‖ := by
  have h := abs_real_inner_le_norm (u t) e
  rwa [norm_u, one_mul] at h

lemma abs_inner_v_le (e : ℝ²) (t : ℝ) : |⟪v t, e⟫| ≤ ‖e‖ := by
  have h := abs_real_inner_le_norm (v t) e
  rwa [norm_v, one_mul] at h

/-- `t ↦ ⟪v_t, e⟫` is `‖e‖`-Lipschitz. -/
lemma abs_inner_v_sub_le (e : ℝ²) (s t : ℝ) : |⟪v s, e⟫ - ⟪v t, e⟫| ≤ ‖e‖ * |s - t| := by
  have hd : ∀ r : ℝ, HasDerivAt (fun r => ⟪e, v r⟫) (-⟪e, u r⟫) r := by
    intro r
    have h := (hasDerivAt_inner_v e r).neg
    have e1 : (-fun s : ℝ => -⟪e, v s⟫) = fun s : ℝ => ⟪e, v s⟫ := by funext s; simp
    rwa [e1] at h
  have hint : (∫ r in t..s, -⟪e, u r⟫) = ⟪e, v s⟫ - ⟪e, v t⟫ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
      (Continuous.intervalIntegrable (by exact (continuous_const.inner continuous_u).neg) t s)
  have hb : ‖∫ r in t..s, -⟪e, u r⟫‖ ≤ ‖e‖ * |s - t| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun r _ => by
      rw [norm_neg, Real.norm_eq_abs, real_inner_comm (u r) e]
      exact abs_inner_u_le e r
  rw [hint, Real.norm_eq_abs] at hb
  rw [real_inner_comm (v s) e, real_inner_comm (v t) e] at hb
  exact hb

/-- `tan x ≤ 2x` on `[0,1]`. -/
lemma tan_le_two_mul {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : tan x ≤ 2 * x := by
  have hpi := pi_gt_three
  have hc : (1 : ℝ) / 2 ≤ cos x := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi hx (by linarith) (by linarith : x ≤ π / 3)
    rwa [cos_pi_div_three] at h
  have hs : sin x ≤ x := by
    rcases eq_or_lt_of_le hx with rfl | h
    · simp
    · exact (sin_lt h).le
  rw [tan_eq_sin_div_cos, div_le_iff₀ (by linarith)]
  nlinarith

/-! ## Integrability and additivity -/

lemma integrableOn_inner_v (K : Set ℝ²) (e : ℝ²) (a b : ℝ) :
    IntegrableOn (fun t => ⟪v t, e⟫) (Ioc a b) (sigmaK K) :=
  (ContinuousOn.integrableOn_compact isCompact_Icc
    (Continuous.continuousOn (continuous_v.inner continuous_const))).mono_set Ioc_subset_Icc_self

lemma setIntegral_inner_v_split (K : Set ℝ²) (e : ℝ²) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∫ t in Ioc a c, ⟪v t, e⟫ ∂(sigmaK K))
      = (∫ t in Ioc a b, ⟪v t, e⟫ ∂(sigmaK K)) + ∫ t in Ioc b c, ⟪v t, e⟫ ∂(sigmaK K) := by
  have hdisj : Disjoint (Ioc a b) (Ioc b c) :=
    Set.disjoint_left.2 fun x hx hx' => absurd hx'.1 (not_lt.2 hx.2)
  rw [← Set.Ioc_union_Ioc_eq_Ioc hab hbc,
    setIntegral_union hdisj measurableSet_Ioc (integrableOn_inner_v K e a b)
      (integrableOn_inner_v K e b c)]

/-! ## The small-interval estimate -/

/-- On a short interval the vertex increment is `⟪v_b, e⟫ σ_K((a,b])` up to `5‖e‖δσ_K((a,b])`. -/
lemma abs_defect_le (hK : IsCompact K) (hne : K.Nonempty) (e : ℝ²) {a b : ℝ}
    (hab : a ≤ b) (hδ : b - a ≤ 1) :
    |⟪vtxP K b - vtxP K a, e⟫ - ∫ t in Ioc a b, ⟪v t, e⟫ ∂(sigmaK K)|
      ≤ 5 * ‖e‖ * (b - a) * (arcFn K b - arcFn K a) := by
  have hpi := pi_gt_three
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = b - a := ⟨_, rfl⟩
  obtain ⟨sr, hsrdef⟩ : ∃ s : ℝ, s = arcFn K b - arcFn K a := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδdef]; linarith
  have hδ1 : δ ≤ 1 := by rw [hδdef]; linarith
  have hδπ : b - a < π / 2 := by linarith
  have hsr0 : 0 ≤ sr := by rw [hsrdef]; linarith [arcFn_mono hK hne hab]
  have hne' : ‖e‖ ≥ 0 := norm_nonneg e
  have htan0 : 0 ≤ tan δ := tan_nonneg_of_nonneg_of_le_pi_div_two hδ0 (by linarith)
  have htan : tan δ ≤ 2 * δ := tan_le_two_mul hδ0 hδ1
  -- the two-sided bounds
  have hu0 : 0 ≤ ⟪vtxP K b - vtxP K a, u b⟫ := inner_vtxP_sub_u_nonneg hK hne a b
  have hv0 : 0 ≤ ⟪vtxP K b - vtxP K a, v b⟫ := inner_vtxP_sub_v_nonneg hK hne hab hδπ
  have hvle : ⟪vtxP K b - vtxP K a, v b⟫ ≤ sr := by
    rw [hsrdef]; exact inner_vtxP_sub_v_le_arcFn hK hne hab
  have hule : ⟪vtxP K b - vtxP K a, u b⟫ ≤ tan δ * sr := by
    have h1 := inner_vtxP_sub_u_le_tan hK hne hab hδπ
    rw [← hδdef] at h1
    nlinarith
  have hvge : sr - ⟪vtxP K b - vtxP K a, v b⟫ ≤ δ * (tan δ * sr) := by
    have h := arcFn_sub_le hK hne hab hδπ
    rw [← hδdef, ← hsrdef] at h
    exact h
  -- the integral
  have hmass : (sigmaK K (Ioc a b)).toReal = sr := by
    rw [sigmaK_Ioc_toReal hK hne hab, hsrdef]
  have hfin : sigmaK K (Ioc a b) < ⊤ := lt_top_iff_ne_top.2 (sigmaK_Ioc_ne_top hK hne a b)
  have hconst : (∫ _t in Ioc a b, ⟪v b, e⟫ ∂(sigmaK K)) = sr * ⟪v b, e⟫ := by
    rw [setIntegral_const, smul_eq_mul, Measure.real, hmass]
  have hsub : (∫ t in Ioc a b, (⟪v t, e⟫ - ⟪v b, e⟫) ∂(sigmaK K))
      = (∫ t in Ioc a b, ⟪v t, e⟫ ∂(sigmaK K)) - ∫ _t in Ioc a b, ⟪v b, e⟫ ∂(sigmaK K) :=
    integral_sub (integrableOn_inner_v K e a b) (integrableOn_const_sigmaK K (⟪v b, e⟫) a b)
  have hsplit : (∫ t in Ioc a b, ⟪v t, e⟫ ∂(sigmaK K))
      = (∫ t in Ioc a b, (⟪v t, e⟫ - ⟪v b, e⟫) ∂(sigmaK K)) + sr * ⟪v b, e⟫ := by
    rw [hsub, hconst]; ring
  have hR : |∫ t in Ioc a b, (⟪v t, e⟫ - ⟪v b, e⟫) ∂(sigmaK K)| ≤ (‖e‖ * δ) * sr := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := sigmaK K) (s := Ioc a b)
      (f := fun t => ⟪v t, e⟫ - ⟪v b, e⟫) (C := ‖e‖ * δ) hfin ?_
    · rw [Real.norm_eq_abs, Measure.real, hmass] at h; exact h
    · intro t ht
      rw [Real.norm_eq_abs]
      refine (abs_inner_v_sub_le e t b).trans ?_
      have : |t - b| ≤ δ := by
        rw [abs_of_nonpos (by linarith [ht.2]), hδdef]
        linarith [ht.1]
      nlinarith
  -- combine
  rw [inner_expand _ e b, hsplit]
  have hA : |⟪vtxP K b - vtxP K a, u b⟫ * ⟪u b, e⟫| ≤ (2 * δ * sr) * ‖e‖ := by
    rw [abs_mul]
    refine mul_le_mul ?_ (abs_inner_u_le e b) (abs_nonneg _) (by nlinarith)
    rw [abs_of_nonneg hu0]; nlinarith
  have hB : |(⟪vtxP K b - vtxP K a, v b⟫ - sr) * ⟪v b, e⟫| ≤ (2 * δ * sr) * ‖e‖ := by
    rw [abs_mul]
    refine mul_le_mul ?_ (abs_inner_v_le e b) (abs_nonneg _) (by nlinarith)
    rw [abs_of_nonpos (by linarith), neg_sub]; nlinarith
  obtain ⟨A, hA'⟩ : ∃ A : ℝ, A = ⟪vtxP K b - vtxP K a, u b⟫ * ⟪u b, e⟫ := ⟨_, rfl⟩
  obtain ⟨B, hB'⟩ : ∃ B : ℝ, B = (⟪vtxP K b - vtxP K a, v b⟫ - sr) * ⟪v b, e⟫ := ⟨_, rfl⟩
  obtain ⟨R, hR'⟩ : ∃ R : ℝ, R = ∫ t in Ioc a b, (⟪v t, e⟫ - ⟪v b, e⟫) ∂(sigmaK K) := ⟨_, rfl⟩
  rw [← hA'] at hA
  rw [← hB'] at hB
  rw [← hR'] at hR ⊢
  have heq : ⟪vtxP K b - vtxP K a, u b⟫ * ⟪u b, e⟫
      + ⟪vtxP K b - vtxP K a, v b⟫ * ⟪v b, e⟫ - (R + sr * ⟪v b, e⟫) = A + B - R := by
    rw [hA', hB']; ring
  rw [heq]
  have htri : |A + B - R| ≤ |A| + |B| + |R| := by
    have h1 := abs_add_le (A + B) (-R)
    have h2 := abs_add_le A B
    rw [abs_neg] at h1
    rw [show A + B - R = A + B + -R by ring]
    linarith
  have hgoal : |A| + |B| + |R| ≤ 5 * ‖e‖ * (b - a) * (arcFn K b - arcFn K a) := by
    rw [← hδdef, ← hsrdef]
    nlinarith
  linarith

/-! ## Theorem 5.2.2 -/

/-- **Baek Theorem 5.2.2** (scalar form): `⟪v⁺_K(b) − v⁺_K(a), e⟫ = ∫_{(a,b]} ⟪v_t, e⟫ σ_K(dt)`. -/
theorem inner_vtxP_sub_eq_setIntegral (hK : IsCompact K) (hne : K.Nonempty) (e : ℝ²) {a b : ℝ}
    (hab : a ≤ b) :
    ⟪vtxP K b - vtxP K a, e⟫ = ∫ t in Ioc a b, ⟪v t, e⟫ ∂(sigmaK K) := by
  obtain ⟨D, hD⟩ : ∃ D : ℝ → ℝ → ℝ, D = fun x y =>
      ⟪vtxP K y - vtxP K x, e⟫ - ∫ t in Ioc x y, ⟪v t, e⟫ ∂(sigmaK K) := ⟨_, rfl⟩
  have hadd : ∀ x y z : ℝ, x ≤ y → y ≤ z → D x z = D x y + D y z := by
    intro x y z hxy hyz
    simp only [hD]
    rw [setIntegral_inner_v_split K e hxy hyz]
    have : ⟪vtxP K z - vtxP K x, e⟫
        = ⟪vtxP K y - vtxP K x, e⟫ + ⟪vtxP K z - vtxP K y, e⟫ := by
      rw [← inner_add_left]
      congr 1
      abel
    rw [this]; ring
  -- the chained bound, with mesh `δ`
  have chain : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ n : ℕ, ∀ x y : ℝ, x ≤ y → y ≤ x + n * δ →
      |D x y| ≤ 5 * ‖e‖ * δ * (arcFn K y - arcFn K x) := by
    intro δ hδ0 hδ1 n
    induction n with
    | zero =>
      intro x y hxy hy
      simp only [Nat.cast_zero, zero_mul, add_zero] at hy
      have : x = y := le_antisymm hxy hy
      subst this
      simp [hD]
    | succ n ih =>
      intro x y hxy hy
      rcases le_or_gt y (x + δ) with h1 | h1
      · have hstep : |D x y| ≤ 5 * ‖e‖ * (y - x) * (arcFn K y - arcFn K x) := by
          simp only [hD]
          exact abs_defect_le hK hne e hxy (by linarith)
        have h2 : (0:ℝ) ≤ arcFn K y - arcFn K x := by linarith [arcFn_mono hK hne hxy]
        have hkey : 0 ≤ (5 * ‖e‖ * (δ - (y - x))) * (arcFn K y - arcFn K x) :=
          mul_nonneg (mul_nonneg (by positivity) (by linarith)) h2
        nlinarith [hkey, hstep]
      · have h2 : x + δ ≤ y := h1.le
        have h3 : (0:ℝ) ≤ arcFn K (x + δ) - arcFn K x := by
          linarith [arcFn_mono hK hne (by linarith : x ≤ x + δ)]
        have h4 : (0:ℝ) ≤ arcFn K y - arcFn K (x + δ) := by
          linarith [arcFn_mono hK hne h2]
        have hstep : |D x (x + δ)| ≤ 5 * ‖e‖ * δ * (arcFn K (x + δ) - arcFn K x) := by
          simp only [hD]
          have h := abs_defect_le hK hne e (by linarith : x ≤ x + δ) (by linarith)
          rw [show x + δ - x = δ by ring] at h
          exact h
        have hrest : |D (x + δ) y| ≤ 5 * ‖e‖ * δ * (arcFn K y - arcFn K (x + δ)) := by
          refine ih (x + δ) y h2 ?_
          push_cast at hy ⊢
          linarith
        rw [hadd x (x + δ) y (by linarith) h2]
        refine le_trans (abs_add_le _ _) ?_
        linarith
  -- pass to the limit `δ → 0`
  have hsr0 : (0:ℝ) ≤ arcFn K b - arcFn K a := by linarith [arcFn_mono hK hne hab]
  have hall : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → |D a b| ≤ 5 * ‖e‖ * δ * (arcFn K b - arcFn K a) := by
    intro δ hδ0 hδ1
    obtain ⟨n, hn⟩ := exists_nat_ge ((b - a) / δ)
    exact chain δ hδ0 hδ1 n a b hab (by
      have := (div_le_iff₀ hδ0).1 hn
      linarith)
  have hzero : D a b = 0 := by
    by_contra hcon
    have hpos : 0 < |D a b| := abs_pos.2 hcon
    obtain ⟨c, hcge, hcpos⟩ : ∃ c : ℝ, 5 * ‖e‖ * (arcFn K b - arcFn K a) ≤ c ∧ 0 < c :=
      ⟨5 * ‖e‖ * (arcFn K b - arcFn K a) + 1, by linarith,
        by nlinarith [norm_nonneg e, hsr0]⟩
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min 1 (|D a b| / (2 * c)) := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by
      rw [hδdef]
      exact lt_min one_pos (div_pos hpos (by linarith))
    have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
    have hδ2 : δ ≤ |D a b| / (2 * c) := by rw [hδdef]; exact min_le_right _ _
    have h := hall δ hδ0 hδ1
    have hc2 : c * δ ≤ |D a b| / 2 := by
      have h6 := (le_div_iff₀ (by linarith : (0:ℝ) < 2 * c)).1 hδ2
      linarith
    have h5 : (5 * ‖e‖ * (arcFn K b - arcFn K a)) * δ ≤ c * δ :=
      mul_le_mul_of_nonneg_right hcge hδ0.le
    linarith
  simp only [hD] at hzero
  linarith [hzero]

/-- `t ↦ v_t` is `σ_K`-integrable on every `(a,b]`. -/
lemma integrableOn_v (K : Set ℝ²) (a b : ℝ) : IntegrableOn v (Ioc a b) (sigmaK K) :=
  (ContinuousOn.integrableOn_compact isCompact_Icc
    (Continuous.continuousOn continuous_v)).mono_set Ioc_subset_Icc_self

/-- **Baek Theorem 5.2.2** (vector form): `v⁺_K(b) − v⁺_K(a) = ∫_{(a,b]} v_t σ_K(dt)`. -/
theorem vtxP_sub_eq_setIntegral (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ} (hab : a ≤ b) :
    vtxP K b - vtxP K a = ∫ t in Ioc a b, v t ∂(sigmaK K) := by
  refine ext_inner_left ℝ fun e => ?_
  have h1 : (∫ t in Ioc a b, ⟪e, v t⟫ ∂(sigmaK K))
      = ∫ t in Ioc a b, ⟪v t, e⟫ ∂(sigmaK K) :=
    setIntegral_congr_fun measurableSet_Ioc fun t _ => real_inner_comm (v t) e
  rw [real_inner_comm (vtxP K b - vtxP K a) e, inner_vtxP_sub_eq_setIntegral hK hne e hab,
    ← h1, _root_.integral_inner (integrableOn_v K a b) e]

end Sofa
