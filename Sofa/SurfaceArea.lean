/-
# Sofa/SurfaceArea.lean — the surface area measure `σ_K` (Baek Chapter 5)

Mathlib (v4.33.1) has no vector-valued Lebesgue–Stieltjes measure for functions of bounded
variation, so instead of *deriving* `σ_K` from `d v⁺_K` we **define** it as an ordinary
Lebesgue–Stieltjes measure and then prove `d v⁺_K = v_t σ_K` (Thm 5.2.2) as a theorem.

The definition comes from the product rule: if `d v⁺_K = v_t σ_K(dt)` then, since
`d/dt v_t = −u_t` and `⟪v⁺_K(t), u_t⟫ = h_K(t)`,

    d ⟪v⁺_K(t), v_t⟫ = σ_K(dt) − h_K(t) dt,

so `σ_K((a,b]) = ⟪v⁺_K(b), v_b⟫ − ⟪v⁺_K(a), v_a⟫ + ∫_a^b h_K`.  We take the right-hand side as
the definition of the generating function

    `arcFn K t = ⟪v⁺_K(t), v_t⟫ + ∫_0^t h_K`.

`arcFn K` is right-continuous because `v⁺_K` is (Thm 2.1.3), and monotone because of the
one-line geometric fact `⟪v⁺_K(b) − v⁺_K(a), v_b⟫ ≥ 0` for `0 ≤ b − a < π/2`
(`inner_vtxP_sub_v_nonneg`).

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.Vertex

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²}

/-! ## A chaining lemma for monotonicity -/

/-- A function that is monotone on every interval of a *fixed* positive length is monotone. -/
lemma monotone_of_locally {f : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x y : ℝ, x ≤ y → y ≤ x + δ → f x ≤ f y) : Monotone f := by
  have key : ∀ n : ℕ, ∀ x y : ℝ, x ≤ y → y ≤ x + n * δ → f x ≤ f y := by
    intro n
    induction n with
    | zero => intro x y hxy hy; simp only [Nat.cast_zero, zero_mul, add_zero] at hy;
              rw [le_antisymm hxy hy]
    | succ n ih =>
      intro x y hxy hy
      rcases le_or_gt y (x + δ) with h1 | h1
      · exact h x y hxy h1
      · refine le_trans (h x (x + δ) (by linarith) le_rfl) (ih (x + δ) y h1.le ?_)
        push_cast at hy ⊢
        linarith
  intro x y hxy
  obtain ⟨n, hn⟩ := exists_nat_ge ((y - x) / δ)
  refine key n x y hxy ?_
  have := (div_le_iff₀ hδ).1 hn
  linarith

/-! ## The basic geometric inequality -/

/-- `u_a = cos(a−b) u_b + sin(a−b) v_b`. -/
lemma inner_u_rotate (p : ℝ²) (a b : ℝ) :
    ⟪p, u a⟫ = cos (a - b) * ⟪p, u b⟫ + sin (a - b) * ⟪p, v b⟫ := by
  simp only [inner_eq, u_coord_zero, u_coord_one, v_coord_zero, v_coord_one]
  have h1 : cos a = cos (a - b) * cos b - sin (a - b) * sin b := by
    rw [← cos_add, show a - b + b = a by ring]
  have h2 : sin a = cos (a - b) * sin b + sin (a - b) * cos b := by
    rw [show sin a = sin (a - b + b) from by rw [show a - b + b = a by ring], sin_add]; ring
  rw [h1, h2]; ring

/-- The vertex always moves *forward*: `⟪v⁺_K(b) − v⁺_K(a), u_b⟫ ≥ 0`. -/
lemma inner_vtxP_sub_u_nonneg (hK : IsCompact K) (hne : K.Nonempty) (a b : ℝ) :
    0 ≤ ⟪vtxP K b - vtxP K a, u b⟫ := by
  rw [inner_sub_left, inner_vtxP_u, sub_nonneg]
  exact le_supportFn hK (vtxP_mem hK hne a) b

/-- **The key inequality** (raw form): `cos(b−a) ⟪d, u_b⟫ ≤ sin(b−a) ⟪d, v_b⟫` for
`d = v⁺_K(b) − v⁺_K(a)`.  It comes from `⟪v⁺_K(b), u_a⟫ ≤ h_K(a) = ⟪v⁺_K(a), u_a⟫`. -/
lemma cos_mul_inner_vtxP_sub_le (hK : IsCompact K) (hne : K.Nonempty) (a b : ℝ) :
    cos (b - a) * ⟪vtxP K b - vtxP K a, u b⟫ ≤ sin (b - a) * ⟪vtxP K b - vtxP K a, v b⟫ := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ², d = vtxP K b - vtxP K a := ⟨_, rfl⟩
  have hq : ⟪d, u a⟫ ≤ 0 := by
    rw [hd, inner_sub_left, inner_vtxP_u, sub_nonpos]
    exact le_supportFn hK (vtxP_mem hK hne b) a
  have hdec := inner_u_rotate d a b
  have e1 : cos (a - b) = cos (b - a) := by rw [show a - b = -(b - a) by ring, cos_neg]
  have e2 : sin (a - b) = -sin (b - a) := by rw [show a - b = -(b - a) by ring, sin_neg]
  rw [e1, e2] at hdec
  rw [← hd]
  linarith

/-- **The key inequality.**  For `0 ≤ b − a < π/2` the vertex moves in the direction `v_b`:
`⟪v⁺_K(b) − v⁺_K(a), v_b⟫ ≥ 0`. -/
lemma inner_vtxP_sub_v_nonneg (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ} (hab : a ≤ b)
    (hlt : b - a < π / 2) : 0 ≤ ⟪vtxP K b - vtxP K a, v b⟫ := by
  have hp := inner_vtxP_sub_u_nonneg hK hne a b
  have hkey := cos_mul_inner_vtxP_sub_le hK hne a b
  rcases eq_or_lt_of_le hab with rfl | hlt'
  · simp
  · have hs : 0 < sin (b - a) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
    have hc : 0 < cos (b - a) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hlt⟩
    nlinarith

/-- `⟪v⁺_K(b) − v⁺_K(a), u_b⟫ ≤ tan(b−a) ⟪v⁺_K(b) − v⁺_K(a), v_b⟫`. -/
lemma inner_vtxP_sub_u_le_tan (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ} (hab : a ≤ b)
    (hlt : b - a < π / 2) :
    ⟪vtxP K b - vtxP K a, u b⟫ ≤ tan (b - a) * ⟪vtxP K b - vtxP K a, v b⟫ := by
  have hc : 0 < cos (b - a) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hlt⟩
  have hkey := cos_mul_inner_vtxP_sub_le hK hne a b
  rw [tan_eq_sin_div_cos]
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  linarith

/-! ## The generating function -/

/-- `t ↦ ⟪v⁺_K(t), v_t⟫ + ∫_0^t h_K`: a monotone right-continuous function whose
Lebesgue–Stieltjes measure is the surface area measure `σ_K`. -/
def arcFn (K : Set ℝ²) (t : ℝ) : ℝ := ⟪vtxP K t, v t⟫ + ∫ s in (0:ℝ)..t, supportFn K s

lemma hasDerivAt_inner_v (p : ℝ²) (t : ℝ) :
    HasDerivAt (fun s => -⟪p, v s⟫) ⟪p, u t⟫ t := by
  have h := ((hasDerivAt_sin t).const_mul (p 0)).sub ((hasDerivAt_cos t).const_mul (p 1))
  have e : p 0 * cos t - p 1 * -sin t = p 0 * cos t + p 1 * sin t := by ring
  rw [e] at h
  have e1 : (fun s => -⟪p, v s⟫) = fun s => p 0 * sin s - p 1 * cos s := by
    funext s; rw [inner_eq, v_coord_zero, v_coord_one]; ring
  have e2 : ⟪p, u t⟫ = p 0 * cos t + p 1 * sin t := by rw [inner_eq, u_coord_zero, u_coord_one]
  rw [e1, e2]
  exact h

/-- `∫_a^b ⟪p, u_s⟫ ds = ⟪p, v_a⟫ − ⟪p, v_b⟫`. -/
lemma integral_inner_u (p : ℝ²) (a b : ℝ) :
    ∫ s in a..b, ⟪p, u s⟫ = ⟪p, v a⟫ - ⟪p, v b⟫ := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => -⟪p, v s⟫)
    (f' := fun s => ⟪p, u s⟫) (a := a) (b := b) (fun s _ => hasDerivAt_inner_v p s) ?_
  · rw [h]; ring
  · exact (Continuous.intervalIntegrable (continuous_const.inner continuous_u) a b)

lemma integrable_supportFn (hK : IsCompact K) (hne : K.Nonempty) (a b : ℝ) :
    IntervalIntegrable (supportFn K) volume a b :=
  (continuous_supportFn hK hne).intervalIntegrable a b

lemma arcFn_sub (hK : IsCompact K) (hne : K.Nonempty) (a b : ℝ) :
    arcFn K b - arcFn K a
      = ⟪vtxP K b, v b⟫ - ⟪vtxP K a, v a⟫ + ∫ s in a..b, supportFn K s := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (integrable_supportFn hK hne 0 a) (integrable_supportFn hK hne a b)
  rw [arcFn, arcFn, ← h]
  ring

lemma arcFn_mono (hK : IsCompact K) (hne : K.Nonempty) : Monotone (arcFn K) := by
  refine monotone_of_locally (δ := 1) one_pos ?_
  intro a b hab hb
  have hlt : b - a < π / 2 := by linarith [pi_gt_three]
  rw [← sub_nonneg, arcFn_sub hK hne]
  -- `∫_a^b h ≥ ∫_a^b ⟪v⁺_K(a), u_s⟫ = ⟪v⁺_K(a), v_a⟫ − ⟪v⁺_K(a), v_b⟫`
  have hint : (∫ s in a..b, ⟪vtxP K a, u s⟫) ≤ ∫ s in a..b, supportFn K s := by
    refine intervalIntegral.integral_mono_on hab
      (Continuous.intervalIntegrable (continuous_const.inner continuous_u) a b)
      (integrable_supportFn hK hne a b) ?_
    intro s _
    exact le_supportFn hK (vtxP_mem hK hne a) s
  rw [integral_inner_u] at hint
  have hkey := inner_vtxP_sub_v_nonneg hK hne hab hlt
  rw [inner_sub_left] at hkey
  linarith

lemma continuous_primitive_supportFn (hK : IsCompact K) (hne : K.Nonempty) :
    Continuous fun t => ∫ s in (0:ℝ)..t, supportFn K s :=
  intervalIntegral.continuous_primitive (fun a b => integrable_supportFn hK hne a b) 0

lemma arcFn_right_continuous (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    ContinuousWithinAt (arcFn K) (Ici t) t := by
  have h1 : ContinuousWithinAt (fun s => ⟪vtxP K s, v s⟫) (Ici t) t := by
    have h2 : Tendsto (fun s => ⟪vtxP K s, v s⟫) (𝓝[>] t) (𝓝 ⟪vtxP K t, v t⟫) := by
      have ha := tendsto_vtxP_right hK hne t
      have hb : Tendsto (fun s : ℝ => v s) (𝓝[>] t) (𝓝 (v t)) :=
        ((continuous_v).tendsto t).mono_left nhdsWithin_le_nhds
      exact ha.inner hb
    rw [← continuousWithinAt_Ioi_iff_Ici]
    exact h2
  exact h1.add ((continuous_primitive_supportFn hK hne).continuousWithinAt)

/-! ## The two-sided estimate `d v⁺_K ≈ v_t σ_K` -/

/-- `σ_K((a,b]) − ⟪v⁺_K(b) − v⁺_K(a), v_b⟫ = ∫_a^b (h_K(s) − ⟪v⁺_K(a), u_s⟫) ds`. -/
lemma arcFn_sub_sub_inner (hK : IsCompact K) (hne : K.Nonempty) (a b : ℝ) :
    arcFn K b - arcFn K a - ⟪vtxP K b - vtxP K a, v b⟫
      = ∫ s in a..b, (supportFn K s - ⟪vtxP K a, u s⟫) := by
  rw [arcFn_sub hK hne, intervalIntegral.integral_sub (integrable_supportFn hK hne a b)
      (Continuous.intervalIntegrable (continuous_const.inner continuous_u) a b),
    integral_inner_u, inner_sub_left]
  ring

/-- Lower bound: `⟪v⁺_K(b) − v⁺_K(a), v_b⟫ ≤ σ_K((a,b])`. -/
lemma inner_vtxP_sub_v_le_arcFn (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ} (hab : a ≤ b) :
    ⟪vtxP K b - vtxP K a, v b⟫ ≤ arcFn K b - arcFn K a := by
  rw [← sub_nonneg, arcFn_sub_sub_inner hK hne]
  refine intervalIntegral.integral_nonneg hab fun s _ => ?_
  rw [sub_nonneg]
  exact le_supportFn hK (vtxP_mem hK hne a) s

/-- The integrand of `arcFn_sub_sub_inner` is `⟪v⁺_K(s) − v⁺_K(a), u_s⟫`. -/
lemma supportFn_sub_inner_vtxP (K : Set ℝ²) (a s : ℝ) :
    supportFn K s - ⟪vtxP K a, u s⟫ = ⟪vtxP K s - vtxP K a, u s⟫ := by
  rw [inner_sub_left, inner_vtxP_u]

/-- `tan` is monotone on `[0, π/2)`. -/
lemma tan_le_tan_of_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y < π / 2) :
    tan x ≤ tan y := by
  rcases eq_or_lt_of_le hxy with rfl | h
  · exact le_rfl
  · exact (tan_lt_tan_of_nonneg_of_lt_pi_div_two hx hy h).le

/-- Upper bound: `σ_K((a,b]) ≤ ⟪v⁺_K(b) − v⁺_K(a), v_b⟫ + (b−a) tan(b−a) σ_K((a,b])`. -/
lemma arcFn_sub_le (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ} (hab : a ≤ b)
    (hlt : b - a < π / 2) :
    arcFn K b - arcFn K a - ⟪vtxP K b - vtxP K a, v b⟫
      ≤ (b - a) * (tan (b - a) * (arcFn K b - arcFn K a)) := by
  rw [arcFn_sub_sub_inner hK hne]
  have hbnd : ∀ s ∈ Icc a b, supportFn K s - ⟪vtxP K a, u s⟫
      ≤ tan (b - a) * (arcFn K b - arcFn K a) := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hs
    have h1 : supportFn K s - ⟪vtxP K a, u s⟫ ≤ tan (s - a) * ⟪vtxP K s - vtxP K a, v s⟫ := by
      rw [supportFn_sub_inner_vtxP]
      exact inner_vtxP_sub_u_le_tan hK hne hs1 (by linarith)
    have h2 : ⟪vtxP K s - vtxP K a, v s⟫ ≤ arcFn K s - arcFn K a :=
      inner_vtxP_sub_v_le_arcFn hK hne hs1
    have h3 : (0 : ℝ) ≤ arcFn K s - arcFn K a := by
      linarith [inner_vtxP_sub_v_nonneg hK hne hs1 (by linarith : s - a < π / 2), h2]
    have h4 : tan (s - a) ≤ tan (b - a) :=
      tan_le_tan_of_le (by linarith) (by linarith) hlt
    have h5 : (0 : ℝ) ≤ tan (s - a) := tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith)
      (by linarith)
    have h6 : arcFn K s - arcFn K a ≤ arcFn K b - arcFn K a := by
      have := arcFn_mono hK hne hs2
      linarith
    nlinarith
  calc (∫ s in a..b, (supportFn K s - ⟪vtxP K a, u s⟫))
      ≤ ∫ _s in a..b, tan (b - a) * (arcFn K b - arcFn K a) := by
        refine intervalIntegral.integral_mono_on hab ?_ (intervalIntegrable_const) hbnd
        exact ((integrable_supportFn hK hne a b).sub
          (Continuous.intervalIntegrable (continuous_const.inner continuous_u) a b))
    _ = (b - a) * (tan (b - a) * (arcFn K b - arcFn K a)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]

/-! ## The surface area measure -/

/-- `arcFn K` as a bundled Stieltjes function. -/
def arcSF (hK : IsCompact K) (hne : K.Nonempty) : StieltjesFunction ℝ where
  toFun := arcFn K
  mono' := arcFn_mono hK hne
  right_continuous' := arcFn_right_continuous hK hne

@[simp] lemma arcSF_apply (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    arcSF hK hne t = arcFn K t := rfl

/-- **Def 2.1.13 / Thm 2.1.1** (as formalized): the surface area measure `σ_K`, defined as the
Lebesgue–Stieltjes measure of `arcFn K` (and `0` for degenerate `K`). -/
def sigmaK (K : Set ℝ²) : Measure ℝ :=
  open Classical in
  if h : IsCompact K ∧ K.Nonempty then (arcSF h.1 h.2).measure else 0

lemma sigmaK_eq (hK : IsCompact K) (hne : K.Nonempty) : sigmaK K = (arcSF hK hne).measure := by
  classical
  rw [sigmaK, dif_pos ⟨hK, hne⟩]

@[simp] lemma sigmaK_Ioc (hK : IsCompact K) (hne : K.Nonempty) (a b : ℝ) :
    sigmaK K (Ioc a b) = ENNReal.ofReal (arcFn K b - arcFn K a) := by
  rw [sigmaK_eq hK hne]; exact (arcSF hK hne).measure_Ioc a b

instance isLocallyFiniteMeasure_sigmaK (K : Set ℝ²) : IsLocallyFiniteMeasure (sigmaK K) := by
  classical
  by_cases h : IsCompact K ∧ K.Nonempty
  · rw [sigmaK_eq h.1 h.2]; infer_instance
  · rw [sigmaK, dif_neg h]; infer_instance

lemma integrableOn_const_sigmaK (K : Set ℝ²) (c : ℝ) (a b : ℝ) :
    IntegrableOn (fun _ => c) (Ioc a b) (sigmaK K) :=
  (ContinuousOn.integrableOn_compact isCompact_Icc continuousOn_const).mono_set
    Ioc_subset_Icc_self

lemma sigmaK_Ioc_ne_top (hK : IsCompact K) (hne : K.Nonempty) (a b : ℝ) :
    sigmaK K (Ioc a b) ≠ ⊤ := by rw [sigmaK_Ioc hK hne]; exact ENNReal.ofReal_ne_top

lemma sigmaK_Ioc_toReal (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ} (hab : a ≤ b) :
    (sigmaK K (Ioc a b)).toReal = arcFn K b - arcFn K a := by
  rw [sigmaK_Ioc hK hne, ENNReal.toReal_ofReal (by linarith [arcFn_mono hK hne hab])]

/-- `σ_K({t}) = |e_K(t)|`: the atoms of the surface area measure are the edge lengths. -/
theorem sigmaK_singleton (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    sigmaK K {t} = ENNReal.ofReal (edgeLength K t) := by
  rw [sigmaK_eq hK hne, (arcSF hK hne).measure_singleton]
  congr 1
  have hlim : Function.leftLim (⇑(arcSF hK hne)) t
      = ⟪vtxM K t, v t⟫ + ∫ s in (0:ℝ)..t, supportFn K s := by
    refine leftLim_eq_of_tendsto (f := ⇑(arcSF hK hne)) ?_
    have ha := tendsto_vtxP_left hK hne t
    have hb : Tendsto (fun s : ℝ => v s) (𝓝[<] t) (𝓝 (v t)) :=
      ((continuous_v).tendsto t).mono_left nhdsWithin_le_nhds
    exact (ha.inner hb).add
      (((continuous_primitive_supportFn hK hne).tendsto t).mono_left nhdsWithin_le_nhds)
  have h2 : (arcSF hK hne) t = arcFn K t := rfl
  rw [h2, hlim, arcFn, edgeLength, ← inner_vtxP_v, ← inner_vtxM_v]
  ring

/-! ## Countably many atoms; uniform bounds

Moved here from `Sofa/ArmLimit.lean` and `Sofa/AbsCont.lean` in round 42: they are facts about
every convex body, and Baek's Ch. 7–8 modules need them without Ch. 6. -/

/-- A compact nonempty set has a radius bound, and the bound is nonnegative. -/
lemma exists_radius (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ p ∈ K, ‖p‖ ≤ R := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK.isBounded
  obtain ⟨p, hp⟩ := hne
  exact ⟨R, le_trans (norm_nonneg p) (hR p hp), hR⟩

lemma edgeMax_sub_edgeMin (K : Set ℝ²) (t : ℝ) :
    edgeMax K t - edgeMin K t = edgeLength K t := rfl

/-- As `s ↑ t`, `arcFn K s → arcFn K t − |e_K(t)|`: the jump of `arcFn K` at `t` is the edge
length. -/
lemma tendsto_arcFn_nhdsLT (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    Tendsto (arcFn K) (𝓝[<] t) (𝓝 (arcFn K t - edgeLength K t)) := by
  have hv : Tendsto (fun s : ℝ => v s) (𝓝[<] t) (𝓝 (v t)) :=
    (continuous_v.tendsto t).mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun s => ⟪vtxP K s, v s⟫) (𝓝[<] t) (𝓝 ⟪vtxM K t, v t⟫) :=
    (tendsto_vtxP_left hK hne t).inner hv
  have h2 : Tendsto (fun s : ℝ => ∫ r in (0:ℝ)..s, supportFn K r) (𝓝[<] t)
      (𝓝 (∫ r in (0:ℝ)..t, supportFn K r)) :=
    ((continuous_primitive_supportFn hK hne).tendsto t).mono_left nhdsWithin_le_nhds
  have h := h1.add h2
  rw [inner_vtxM_v] at h
  have hval : edgeMin K t + ∫ r in (0:ℝ)..t, supportFn K r
      = arcFn K t - edgeLength K t := by
    rw [arcFn, inner_vtxP_v, ← edgeMax_sub_edgeMin]
    ring
  rw [hval] at h
  exact Tendsto.congr (fun s => rfl) h

/-- `arcFn K` is right-continuous (`v⁺_K` is). -/
lemma tendsto_arcFn_nhdsGT (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    Tendsto (arcFn K) (𝓝[>] t) (𝓝 (arcFn K t)) := by
  have hv : Tendsto (fun s : ℝ => v s) (𝓝[≥] t) (𝓝 (v t)) :=
    (continuous_v.tendsto t).mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun s => ⟪vtxP K s, v s⟫) (𝓝[≥] t) (𝓝 ⟪vtxP K t, v t⟫) :=
    (continuousWithinAt_vtxP hK hne t).inner hv
  have h2 : Tendsto (fun s : ℝ => ∫ r in (0:ℝ)..s, supportFn K r) (𝓝[≥] t)
      (𝓝 (∫ r in (0:ℝ)..t, supportFn K r)) :=
    ((continuous_primitive_supportFn hK hne).tendsto t).mono_left nhdsWithin_le_nhds
  have h := (h1.add h2).mono_left (nhdsWithin_mono t Ioi_subset_Ici_self)
  exact Tendsto.congr (fun s => rfl) h

/-- **The atoms of `σ_K` are countable.** -/
theorem countable_edgeLength_ne_zero (hK : IsCompact K) (hne : K.Nonempty) :
    {t : ℝ | edgeLength K t ≠ 0}.Countable := by
  refine Set.Countable.mono ?_ (arcFn_mono hK hne).countable_not_continuousAt
  intro t ht
  simp only [Set.mem_ofPred_eq] at ht ⊢
  intro hcont
  have h1 : Tendsto (arcFn K) (𝓝[<] t) (𝓝 (arcFn K t)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h2 := tendsto_arcFn_nhdsLT hK hne t
  have heq := tendsto_nhds_unique h1 h2
  exact ht (by linarith)

lemma abs_edgeMax_le {R : ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (hR : ∀ p ∈ K, ‖p‖ ≤ R) (t : ℝ) : |edgeMax K t| ≤ R := by
  have h := abs_real_inner_le_norm (vtxP K t) (v t)
  rw [inner_vtxP_v, norm_v, mul_one] at h
  exact h.trans (hR _ (vtxP_mem hK hne t))

end Sofa
