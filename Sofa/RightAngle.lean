/-
# Sofa/RightAngle.lean — the right rotation angle (Baek §4.2)

* a Cavalieri principle for graph regions restricted in the `x`-direction;
* explicit areas of the parallelogram `P_ω` and of the corner triangles cut off by
  `⟪p, u₀⟫ ≤ c`;
* **Lemma 4.2.2**: `|R_{ω,d}| < 2.2` for `d = d_{ω,min}`;
* **Lemma 4.2.3/4.2.4** and **Theorem 4.2.5**.

STATUS: [PROOF-C-local] round 1 (2026-09-17, Opus 5): compiled in the cloud dev tree, no `sorry`.
-/
import Sofa.SideLength

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {ω : ℝ}

/-! ## Cavalieri with a restricted `x`-range -/

theorem measureReal_between_restrict {S : Set ℝ} (hS : MeasurableSet S) {lo hi : ℝ → ℝ}
    (hlo : Measurable lo) (hhi : Measurable hi)
    (hint : Integrable (S.indicator fun x => max (hi x - lo x) 0)) :
    volume.real {p : ℝ² | p 0 ∈ S ∧ lo (p 0) ≤ p 1 ∧ p 1 ≤ hi (p 0)}
      = ∫ x in S, max (hi x - lo x) 0 := by
  classical
  set lo' : ℝ → ℝ := S.piecewise lo (fun x => hi x + 1) with hlo'def
  have hfun : ∀ x, max (hi x - lo' x) 0 = S.indicator (fun x => max (hi x - lo x) 0) x := by
    intro x
    by_cases hp : x ∈ S
    · rw [hlo'def, Set.piecewise_eq_of_mem _ _ _ hp, Set.indicator_of_mem hp]
    · rw [hlo'def, Set.piecewise_eq_of_notMem _ _ _ hp, Set.indicator_of_notMem hp]
      simp
  have hset : {p : ℝ² | p 0 ∈ S ∧ lo (p 0) ≤ p 1 ∧ p 1 ≤ hi (p 0)}
      = {p : ℝ² | lo' (p 0) ≤ p 1 ∧ p 1 ≤ hi (p 0)} := by
    ext p
    by_cases hp : p 0 ∈ S
    · simp only [mem_ofPred_eq, hp, true_and, hlo'def, Set.piecewise_eq_of_mem _ _ _ hp]
    · simp only [mem_ofPred_eq, hp, false_and, false_iff, not_and, hlo'def,
        Set.piecewise_eq_of_notMem _ _ _ hp]
      intro h1 h2
      linarith
  have hlo'meas : Measurable lo' := Measurable.piecewise hS hlo (hhi.add measurable_const)
  have hint' : Integrable fun x => max (hi x - lo' x) 0 := by
    simpa only [hfun] using hint
  rw [hset, measureReal_between_Icc hlo'meas hhi hint']
  simp_rw [hfun]
  exact integral_indicator hS

/-! ## `c_ω` and the parallelogram `P_ω` -/

/-- **Prop 4.2.1.** `c_ω = sec ω − tan ω = (1 − sin ω)/cos ω`; `o_ω = (c_ω, 1)`. -/
def cw (ω : ℝ) : ℝ := (1 - sin ω) / cos ω

lemma oω_eq (ω : ℝ) : oω ω = pt (cw ω) 1 := rfl

lemma cw_nonneg (hω0 : 0 < ω) (hω1 : ω < π / 2) : 0 ≤ cw ω :=
  div_nonneg (by linarith [sin_le_one ω]) (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩).le

lemma cw_le (hω0 : 0 < ω) (hω1 : ω < π / 2) : cw ω ≤ 1 / cos ω := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  rw [cw, div_le_div_iff_of_pos_right hcω]
  linarith [sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])]

/-- The area of the corner triangle `P_ω ∩ {⟪p, u₀⟫ > c}` for `c_ω ≤ c ≤ sec ω`. -/
theorem measureReal_para_gt (hω0 : 0 < ω) (hω1 : ω < π / 2) {c : ℝ}
    (hc1 : cw ω ≤ c) (hc2 : c ≤ 1 / cos ω) :
    volume.real (para ω ∩ {p : ℝ² | c < p 0})
      = (1 / cos ω - c) * (1 - c * cos ω) / (2 * sin ω) := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  have hcw0 : 0 ≤ cw ω := cw_nonneg hω0 hω1
  set R : ℝ := 1 / cos ω with hR
  set hi : ℝ → ℝ := fun x => (1 - x * cos ω) / sin ω with hhidef
  have hhi : Measurable hi := by fun_prop
  have hhicont : Continuous fun x : ℝ => max (hi x - (0 : ℝ)) 0 := by
    rw [hhidef]; fun_prop
  have hhinn : ∀ x : ℝ, 0 ≤ hi x ↔ x ≤ R := by
    intro x
    show 0 ≤ (1 - x * cos ω) / sin ω ↔ x ≤ 1 / cos ω
    rw [le_div_iff₀ hsω, zero_mul, sub_nonneg, le_div_iff₀ hcω]
  -- the set is a restricted graph region
  have hset : para ω ∩ {p : ℝ² | c < p 0}
      = {p : ℝ² | p 0 ∈ Ioi c ∧ (fun _ : ℝ => (0 : ℝ)) (p 0) ≤ p 1 ∧ p 1 ≤ hi (p 0)} := by
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_para_iff, inner_u_decomp, hhidef]
    constructor
    · rintro ⟨⟨⟨hy0, hy1⟩, -, hle⟩, hx⟩
      exact ⟨hx, hy0, by rw [le_div_iff₀ hsω]; linarith⟩
    · rintro ⟨hx, hy0, hy⟩
      rw [le_div_iff₀ hsω] at hy
      have hx0 : 0 < p.ofLp 0 := lt_of_le_of_lt hcw0 (lt_of_le_of_lt hc1 hx)
      refine ⟨⟨⟨hy0, ?_⟩, by positivity, by linarith⟩, hx⟩
      have hcwlt : cw ω < p.ofLp 0 := lt_of_le_of_lt hc1 hx
      rw [cw, div_lt_iff₀ hcω] at hcwlt
      nlinarith
  -- the integrand vanishes beyond `R`
  have hzero : ∀ x : ℝ, R < x → max (hi x - (0 : ℝ)) 0 = 0 := by
    intro x hx
    have hneg : hi x < 0 := by
      by_contra hcon
      exact absurd ((hhinn x).1 (not_lt.1 hcon)) (not_le.2 hx)
    rw [sub_zero, max_eq_right hneg.le]
  have hind : (Ioi c).indicator (fun x => max (hi x - (0 : ℝ)) 0)
      = (Ioc c R).indicator (fun x => max (hi x - (0 : ℝ)) 0) := by
    funext x
    by_cases h1 : c < x
    · by_cases h2 : x ≤ R
      · rw [indicator_of_mem (mem_Ioi.2 h1), indicator_of_mem (mem_Ioc.2 ⟨h1, h2⟩)]
      · rw [indicator_of_mem (mem_Ioi.2 h1),
          indicator_of_notMem (fun h : x ∈ Ioc c R => h2 h.2), hzero x (not_le.1 h2)]
    · rw [indicator_of_notMem (fun h : x ∈ Ioi c => h1 h),
        indicator_of_notMem (fun h : x ∈ Ioc c R => h1 h.1)]
  have hint : Integrable ((Ioi c).indicator fun x => max (hi x - (0 : ℝ)) 0) := by
    rw [hind, integrable_indicator_iff measurableSet_Ioc]
    exact hhicont.integrableOn_Ioc
  rw [hset, measureReal_between_restrict measurableSet_Ioi measurable_const hhi hint]
  have hsplit : ∫ x in Ioi c, max (hi x - (0 : ℝ)) 0 = ∫ x in Ioc c R, max (hi x - (0 : ℝ)) 0 := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioc, hind]
  have hcongr : ∫ x in Ioc c R, max (hi x - (0 : ℝ)) 0 = ∫ x in Ioc c R, hi x := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    rw [sub_zero, max_eq_left ((hhinn x).2 hx.2)]
  have hlin : ∀ x : ℝ, hi x = (sin ω)⁻¹ - (cos ω / sin ω) * x := by
    intro x
    simp only [hhidef]
    field_simp
  have hI : ∫ x in c..R, hi x = (R - c) * (sin ω)⁻¹ - (cos ω / sin ω) * ((R ^ 2 - c ^ 2) / 2) := by
    rw [intervalIntegral.integral_congr (g := fun x => (sin ω)⁻¹ - (cos ω / sin ω) * x)
      (fun x _ => hlin x)]
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      ((by fun_prop : Continuous fun x : ℝ => (cos ω / sin ω) * x).intervalIntegrable c R),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
      smul_eq_mul]
  rw [hsplit, hcongr, ← intervalIntegral.integral_of_le hc2, hI, hR]
  field_simp
  ring

/-- The area of the trapezoid `P_ω ∩ {⟪p, u₀⟫ ≤ c_ω}`. -/
theorem measureReal_para_le_cw (hω0 : 0 < ω) (hω1 : ω < π / 2) :
    volume.real (para ω ∩ {p : ℝ² | p 0 ≤ cw ω}) = sin ω / cos ω / 2 + cw ω := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  set T : ℝ := sin ω / cos ω with hT
  have hT0 : 0 < T := by rw [hT]; positivity
  have hTcw : -T ≤ cw ω := by
    rw [hT, cw, neg_div', div_le_div_iff_of_pos_right hcω]
    linarith
  set lo : ℝ → ℝ := fun x => max 0 (-(x * cos ω / sin ω)) with hlodef
  have hlom : Measurable lo := by rw [hlodef]; fun_prop
  have hcont : Continuous fun x : ℝ => max ((1 : ℝ) - lo x) 0 := by rw [hlodef]; fun_prop
  have hiff : ∀ x y : ℝ, (-(x * cos ω / sin ω) ≤ y ↔ 0 ≤ x * cos ω + y * sin ω) := by
    intro x y
    rw [neg_le, le_div_iff₀ hsω]
    constructor <;> intro h <;> linarith
  -- the region as a restricted graph region
  have hset : para ω ∩ {p : ℝ² | p 0 ≤ cw ω}
      = {p : ℝ² | p 0 ∈ Icc (-T) (cw ω) ∧ lo (p 0) ≤ p 1 ∧ p 1 ≤ (fun _ : ℝ => (1 : ℝ)) (p 0)} := by
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, mem_para_iff, inner_u_decomp, hlodef,
      max_le_iff]
    constructor
    · rintro ⟨⟨⟨hy0, hy1⟩, hq0, -⟩, hx⟩
      refine ⟨⟨?_, hx⟩, ⟨hy0, (hiff _ _).2 hq0⟩, hy1⟩
      rw [hT, neg_le, le_div_iff₀ hcω]
      nlinarith
    · rintro ⟨⟨-, hx2⟩, ⟨hy0, hy2⟩, hy1⟩
      have hq : 0 ≤ p.ofLp 0 * cos ω + p.ofLp 1 * sin ω := (hiff _ _).1 hy2
      refine ⟨⟨⟨hy0, hy1⟩, hq, ?_⟩, hx2⟩
      rw [cw, le_div_iff₀ hcω] at hx2
      nlinarith
  have hint : Integrable ((Icc (-T) (cw ω)).indicator fun x => max ((1 : ℝ) - lo x) 0) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact hcont.integrableOn_Icc
  rw [hset, measureReal_between_restrict measurableSet_Icc hlom measurable_const hint]
  -- split at `0`
  have hI : ∫ x in Icc (-T) (cw ω), max ((1 : ℝ) - lo x) 0 = T / 2 + cw ω := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hTcw]
    have hi1 : IntervalIntegrable (fun x => max ((1 : ℝ) - lo x) 0) volume (-T) 0 :=
      hcont.intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun x => max ((1 : ℝ) - lo x) 0) volume 0 (cw ω) :=
      hcont.intervalIntegrable _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have e1 : ∫ x in (-T)..(0 : ℝ), max ((1 : ℝ) - lo x) 0
        = ∫ x in (-T)..(0 : ℝ), (1 + (cos ω / sin ω) * x) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le (by linarith)] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hlox : lo x = -(x * cos ω / sin ω) := by
        rw [hlodef]
        refine max_eq_right ?_
        rw [le_neg, neg_zero, div_nonpos_iff]
        right
        exact ⟨by nlinarith, hsω.le⟩
      rw [hlox, max_eq_left]
      · field_simp; ring
      · rw [hT, neg_le, le_div_iff₀ hcω] at hx1
        rw [sub_nonneg, neg_le, le_div_iff₀ hsω]
        nlinarith
    have e2 : ∫ x in (0 : ℝ)..(cw ω), max ((1 : ℝ) - lo x) 0 = ∫ x in (0 : ℝ)..(cw ω), (1 : ℝ) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le (cw_nonneg hω0 hω1)] at hx
      have hlox : lo x = 0 := by
        rw [hlodef]
        refine max_eq_left ?_
        rw [neg_nonpos]
        exact div_nonneg (by nlinarith [hx.1]) hsω.le
      rw [hlox, sub_zero, max_eq_left zero_le_one]
    rw [e1, e2, intervalIntegral.integral_const, smul_eq_mul, mul_one,
      intervalIntegral.integral_add intervalIntegrable_const
        ((by fun_prop : Continuous fun x : ℝ => (cos ω / sin ω) * x).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
      smul_eq_mul]
    rw [hT]
    field_simp
    ring
  rw [hI]

lemma isBounded_para (hω0 : 0 < ω) (hω1 : ω < π / 2) : Bornology.IsBounded (para ω) := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  refine isBounded_iff_forall_norm_le.2 ⟨(1 / cos ω + sin ω / cos ω) + 1, fun p hp => ?_⟩
  obtain ⟨⟨hy0, hy1⟩, hq0, hq1⟩ := mem_para_iff.1 hp
  rw [inner_u_decomp] at hq0 hq1
  have h1 : p.ofLp 0 ≤ 1 / cos ω := by rw [le_div_iff₀ hcω]; nlinarith
  have h2 : -(sin ω / cos ω) ≤ p.ofLp 0 := by rw [neg_le, le_div_iff₀ hcω]; nlinarith
  have hpos1 : (0 : ℝ) ≤ 1 / cos ω := by positivity
  have hpos2 : (0 : ℝ) ≤ sin ω / cos ω := by positivity
  refine norm_le_add_of_abs_coord_le (abs_le.2 ⟨by linarith, by linarith⟩)
    (abs_le.2 ⟨by linarith, hy1⟩)

lemma volume_para_ne_top (hω0 : 0 < ω) (hω1 : ω < π / 2) : volume (para ω) ≠ ⊤ :=
  (isBounded_para hω0 hω1).measure_lt_top.ne

/-- `|P_ω| = sec ω`. -/
theorem measureReal_para (hω0 : 0 < ω) (hω1 : ω < π / 2) :
    volume.real (para ω) = 1 / cos ω := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  have hB : MeasurableSet (para ω ∩ {p : ℝ² | cw ω < p 0}) :=
    (isClosed_para ω).measurableSet.inter (measurableSet_lt measurable_const (measurable_coord 0))
  have hdisj : Disjoint (para ω ∩ {p : ℝ² | p 0 ≤ cw ω}) (para ω ∩ {p : ℝ² | cw ω < p 0}) := by
    rw [Set.disjoint_left]
    rintro p ⟨-, h1⟩ ⟨-, h2⟩
    simp only [mem_ofPred_eq] at h1 h2
    linarith
  have hunion : para ω = (para ω ∩ {p : ℝ² | p 0 ≤ cw ω}) ∪ (para ω ∩ {p : ℝ² | cw ω < p 0}) := by
    ext p
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hp
      rcases le_or_gt (p.ofLp 0) (cw ω) with h | h
      · exact Or.inl ⟨hp, h⟩
      · exact Or.inr ⟨hp, h⟩
    · rintro (⟨hp, -⟩ | ⟨hp, -⟩) <;> exact hp
  have hfinA : volume (para ω ∩ {p : ℝ² | p 0 ≤ cw ω}) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_para_ne_top hω0 hω1) (measure_mono inter_subset_left)
  have hfinB : volume (para ω ∩ {p : ℝ² | cw ω < p 0}) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_para_ne_top hω0 hω1) (measure_mono inter_subset_left)
  rw [hunion, measureReal_def, measure_union hdisj hB, ENNReal.toReal_add hfinA hfinB,
    ← measureReal_def, ← measureReal_def, measureReal_para_le_cw hω0 hω1,
    measureReal_para_gt hω0 hω1 le_rfl (cw_le hω0 hω1), cw]
  field_simp
  ring

/-! ## Lemma 4.2.2: the area of `R_{ω,d}` -/

variable {K : Set ℝ²}

/-- If both `h_K(0)` and `h_K(ω + π/2)` are `< D`, then `K` misses the two corner triangles of
`P_ω`, so `|K| ≤ sec ω − (sec ω − D)(1 − D cos ω)/ sin ω`. -/
theorem measureReal_le_of_supportFn_lt (hω0 : 0 < ω) (hω1 : ω < π / 2) (hK : IsCap K ω)
    {D : ℝ} (hD1 : cw ω ≤ D) (hD2 : D ≤ 1 / cos ω)
    (hs0 : supportFn K 0 < D) (hs1 : supportFn K (ω + π / 2) < D) :
    volume.real K ≤ 1 / cos ω - (1 / cos ω - D) * (1 - D * cos ω) / sin ω := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  set Tr : Set ℝ² := para ω ∩ {p : ℝ² | D < p 0} with hTr
  set Tt : Set ℝ² := para ω ∩ {p : ℝ² | D < ⟪p, u (ω + π / 2)⟫} with hTt
  have hTrmeas : MeasurableSet Tr :=
    (isClosed_para ω).measurableSet.inter (measurableSet_lt measurable_const (measurable_coord 0))
  have hTtmeas : MeasurableSet Tt :=
    (isClosed_para ω).measurableSet.inter
      (measurableSet_lt measurable_const (by fun_prop))
  -- the two triangles are mirror images of each other
  have hmir : mirror ω '' Tr = Tt := by
    ext p
    rw [mem_mirror_image]
    simp only [hTr, hTt, mem_inter_iff, mem_ofPred_eq, mem_para_mirror]
    constructor
    · rintro ⟨hp, hx⟩
      refine ⟨hp, ?_⟩
      have := inner_mirror_u ω 0 p
      rw [inner_u_decomp, cos_zero, sin_zero, mul_one, mul_zero, add_zero, sub_zero] at this
      rwa [← this]
    · rintro ⟨hp, hx⟩
      refine ⟨hp, ?_⟩
      have := inner_mirror_u ω 0 p
      rw [inner_u_decomp, cos_zero, sin_zero, mul_one, mul_zero, add_zero, sub_zero] at this
      rwa [this]
  have hvolTt : volume Tt = volume Tr := by rw [← hmir, volume_mirror_image]
  -- they are disjoint
  have hdisj : Disjoint Tr Tt := by
    rw [Set.disjoint_left]
    rintro p ⟨hp, hx⟩ ⟨-, hy⟩
    simp only [mem_ofPred_eq] at hx hy
    obtain ⟨⟨hy0, hy1⟩, -, -⟩ := mem_para_iff.1 hp
    rw [inner_u_decomp, cos_add_pi_div_two, sin_add_pi_div_two] at hy
    have hcwD : cw ω ≤ D := hD1
    rw [cw, div_le_iff₀ hcω] at hcwD
    have hs1' : sin ω < 1 := by nlinarith [sin_sq_add_cos_sq ω, sin_le_one ω, mul_pos hcω hcω]
    have h1 : D * (1 + sin ω) < cos ω := by
      nlinarith [mul_pos (sub_pos.2 hx) hsω, mul_nonneg (sub_nonneg.2 hy1) hcω.le]
    have h2 : D * cos ω * cos ω < cos ω * (1 - sin ω) := by
      nlinarith [sin_sq_add_cos_sq ω,
        mul_lt_mul_of_pos_right h1 (by linarith : (0 : ℝ) < 1 - sin ω)]
    nlinarith [mul_le_mul_of_nonneg_left hcwD hcω.le]
  -- `K` avoids both
  have hKsub : K ⊆ para ω \ (Tr ∪ Tt) := by
    intro p hp
    refine ⟨hK.subset_para hp, ?_⟩
    rintro (⟨-, hx⟩ | ⟨-, hx⟩) <;> simp only [mem_ofPred_eq] at hx
    · have := le_supportFn hK.isCompact hp 0
      rw [inner_u_decomp, cos_zero, sin_zero, mul_one, mul_zero, add_zero] at this
      linarith
    · linarith [le_supportFn hK.isCompact hp (ω + π / 2)]
  -- measure arithmetic
  have hparafin := volume_para_ne_top hω0 hω1
  have hU : Tr ∪ Tt ⊆ para ω := union_subset inter_subset_left inter_subset_left
  have hUmeas : NullMeasurableSet (Tr ∪ Tt) volume := (hTrmeas.union hTtmeas).nullMeasurableSet
  have hUfin : volume (Tr ∪ Tt) ≠ ⊤ := ne_top_of_le_ne_top hparafin (measure_mono hU)
  have hTrfin : volume Tr ≠ ⊤ := ne_top_of_le_ne_top hparafin (measure_mono inter_subset_left)
  have hTtfin : volume Tt ≠ ⊤ := ne_top_of_le_ne_top hparafin (measure_mono inter_subset_left)
  have hdifffin : volume (para ω \ (Tr ∪ Tt)) ≠ ⊤ :=
    ne_top_of_le_ne_top hparafin (measure_mono sdiff_subset)
  have hsum : volume.real (Tr ∪ Tt) = volume.real Tr + volume.real Tt := by
    rw [measureReal_def, measureReal_def, measureReal_def, measure_union hdisj hTtmeas,
      ENNReal.toReal_add hTrfin hTtfin]
  have heq : volume.real (para ω \ (Tr ∪ Tt)) = volume.real (para ω) - volume.real (Tr ∪ Tt) := by
    rw [measureReal_def, measureReal_def, measureReal_def,
      measure_sdiff hU hUmeas hUfin, ENNReal.toReal_sub_of_le (measure_mono hU) hparafin]
  have hTrval : volume.real Tr = (1 / cos ω - D) * (1 - D * cos ω) / (2 * sin ω) :=
    measureReal_para_gt hω0 hω1 hD1 hD2
  have hTtval : volume.real Tt = volume.real Tr := by rw [measureReal_def, hvolTt, measureReal_def]
  calc volume.real K ≤ volume.real (para ω \ (Tr ∪ Tt)) := measureReal_mono hKsub hdifffin
    _ = volume.real (para ω) - (volume.real Tr + volume.real Tt) := by rw [heq, hsum]
    _ = 1 / cos ω - (1 / cos ω - D) * (1 - D * cos ω) / sin ω := by
        rw [measureReal_para hω0 hω1, hTtval, hTrval]
        field_simp
        ring

/-! ## Lemma 4.2.2: the numerical bound -/

/-- **Def 4.2.2.** `d_{ω,min}`: `1.25` when `ω < arctan 2.2` (i.e. `sin ω < 2.2 cos ω`), and
`1.1` otherwise. -/
def dmin (ω : ℝ) : ℝ := if sin ω < (11 / 5) * cos ω then 5 / 4 else 11 / 10

lemma one_le_dmin (ω : ℝ) : 1 ≤ dmin ω := by
  rw [dmin]; split <;> norm_num

lemma dmin_le_two (ω : ℝ) : dmin ω ≤ 2 := by
  rw [dmin]; split <;> norm_num

/-- `d_{ω,min} ≤ tan ω` for `ω ∈ [arccos(5/11), π/2)`. -/
lemma dmin_mul_cos_le_sin (hω0 : 0 < ω) (hω1 : ω < π / 2) (hcos : cos ω ≤ 5 / 11) :
    dmin ω * cos ω ≤ sin ω := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  have hpy := sin_sq_add_cos_sq ω
  rw [dmin]
  split
  · -- `d = 5/4`: use `sin ω ≥ √96/11 > 5/4 · 5/11`
    have hs2 : (96 : ℝ) / 121 ≤ sin ω ^ 2 := by nlinarith
    nlinarith
  · -- `d = 11/10`: `sin ω ≥ 2.2 cos ω ≥ 1.1 cos ω`
    rename_i hcase
    push Not at hcase
    nlinarith

/-- **Lemma 4.2.2.** A cap whose two support values are `< d_{ω,min} + c_ω` has area `< 2.2`. -/
theorem measureReal_lt_of_supportFn_lt (hω0 : 0 < ω) (hω1 : ω < π / 2) (hcos : cos ω ≤ 5 / 11)
    (hK : IsCap K ω) (hs0 : supportFn K 0 < dmin ω + cw ω)
    (hs1 : supportFn K (ω + π / 2) < dmin ω + cw ω) : volume.real K < 11 / 5 := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  have hpy := sin_sq_add_cos_sq ω
  have hd1 := one_le_dmin ω
  have hdtan := dmin_mul_cos_le_sin hω0 hω1 hcos
  set d : ℝ := dmin ω with hd
  set D : ℝ := d + cw ω with hD
  have hD1 : cw ω ≤ D := by rw [hD]; linarith
  have hD2 : D ≤ 1 / cos ω := by
    rw [hD, cw, ← sub_nonneg]
    have hrw : 1 / cos ω - (d + (1 - sin ω) / cos ω) = (sin ω - d * cos ω) / cos ω := by
      field_simp
      ring
    rw [hrw]
    exact div_nonneg (by linarith) hcω.le
  refine lt_of_le_of_lt (measureReal_le_of_supportFn_lt hω0 hω1 hK hD1 hD2 hs0 hs1) ?_
  have hcs : (0 : ℝ) < cos ω * sin ω := by positivity
  refine lt_of_mul_lt_mul_right ?_ hcs.le
  have hexp : (1 / cos ω - (1 / cos ω - D) * (1 - D * cos ω) / sin ω) * (cos ω * sin ω)
      = sin ω * (1 - sin ω) + 2 * d * cos ω * sin ω - d ^ 2 * cos ω ^ 2 := by
    rw [hD, cw]
    field_simp
    ring
  rw [hexp]
  have hs1' : sin ω < 1 := by nlinarith [mul_pos hcω hcω]
  rw [hd, dmin]
  split
  · -- `d = 5/4`
    rename_i hcase
    have h5s11c : 5 * sin ω < 11 * cos ω := by linarith
    have hsq : 25 * sin ω ^ 2 < 121 * cos ω ^ 2 := by nlinarith
    have hc2 : (25 : ℝ) < 146 * cos ω ^ 2 := by nlinarith
    have hs911 : sin ω ≤ 911 / 1000 := by nlinarith
    nlinarith [mul_le_mul hcos hs911 hsω.le (by norm_num : (0 : ℝ) ≤ 5 / 11)]
  · -- `d = 11/10`
    nlinarith [mul_pos (sub_pos.2 hs1') (by linarith : (0 : ℝ) < 21 * sin ω + 121)]

/-! ## Lemma 4.2.4: the numerical inequalities -/

/-- On `[arccos(5/11), π/2)` one has `sin ω ≥ 0.8907`. -/
lemma sin_ge_of_cos_le (hω0 : 0 < ω) (hω1 : ω < π / 2) (hcos : cos ω ≤ 5 / 11) :
    8907 / 10000 ≤ sin ω := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  have hpy := sin_sq_add_cos_sq ω
  nlinarith [mul_le_mul hcos hcos hcω.le (by norm_num : (0 : ℝ) ≤ 5 / 11)]

/-- If moreover `tan ω ≥ 2.2` then `cos²ω ≤ 25/146` and `sin ω ≥ 0.9103`. -/
lemma sin_ge_of_tan_ge (hω0 : 0 < ω) (hω1 : ω < π / 2) (h : (11 / 5) * cos ω ≤ sin ω) :
    cos ω ^ 2 ≤ 25 / 146 ∧ 9103 / 10000 ≤ sin ω := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  have hpy := sin_sq_add_cos_sq ω
  have hsq : (121 / 25) * cos ω ^ 2 ≤ sin ω ^ 2 := by nlinarith
  have hc2 : cos ω ^ 2 ≤ 25 / 146 := by nlinarith
  exact ⟨hc2, by nlinarith⟩

/-- **Lemma 4.2.4 (1).** `d_{ω,min} sin ω > 1`. -/
theorem one_lt_dmin_mul_sin (hω0 : 0 < ω) (hω1 : ω < π / 2) (hcos : cos ω ≤ 5 / 11) :
    1 < dmin ω * sin ω := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  rw [dmin]
  split
  · linarith [sin_ge_of_cos_le hω0 hω1 hcos]
  · rename_i hcase
    push Not at hcase
    linarith [(sin_ge_of_tan_ge hω0 hω1 hcase).2]

/-- The core numerical inequality behind **Lemma 4.2.4 (2)**: `d²cos ω + 4 cos ω sin²ω <
2 d sin ω` for `d = d_{ω,min}`. -/
theorem dmin_ineq (hω0 : 0 < ω) (hω1 : ω < π / 2) (hcos : cos ω ≤ 5 / 11) :
    dmin ω ^ 2 * cos ω + 4 * cos ω * sin ω ^ 2 < 2 * dmin ω * sin ω := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  have hpy := sin_sq_add_cos_sq ω
  have hs1 : sin ω ≤ 1 := sin_le_one ω
  rw [dmin]
  split
  · -- `d = 5/4`: `cos ω ≤ 5/11`, `sin ω ≥ 0.8907`, `sin²ω ≤ 121/146`
    rename_i hcase
    have hs0 := sin_ge_of_cos_le hω0 hω1 hcos
    have hc2 : 25 / 146 ≤ cos ω ^ 2 := by nlinarith
    have hs2 : sin ω ^ 2 ≤ 121 / 146 := by nlinarith
    nlinarith [mul_le_mul hcos hs2 (sq_nonneg (sin ω)) (by norm_num : (0 : ℝ) ≤ 5 / 11)]
  · -- `d = 11/10`: split on `cos ω ≤ 0.31`
    rename_i hcase
    push Not at hcase
    rcases le_or_gt (cos ω) (31 / 100) with hc | hc
    · have hs95 : 9507 / 10000 ≤ sin ω := by nlinarith
      nlinarith
    · nlinarith

/-! ## Mirror symmetry of polygon caps -/

section MirrorPoly

variable {Θ : Finset ℝ}

lemma sub_mem_uniformAngles {n : ℕ} {t : ℝ} (ht : t ∈ uniformAngles ω n) :
    ω - t ∈ uniformAngles ω n := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
  obtain ⟨hi0, hin⟩ := Finset.mem_Ioo.1 hi
  have hn : 0 < n := lt_trans hi0 hin
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine Finset.mem_image.2 ⟨n - i, Finset.mem_Ioo.2 ⟨by omega, by omega⟩, ?_⟩
  have hc : ((n - i : ℕ) : ℝ) = (n : ℝ) - (i : ℝ) := by
    rw [Nat.cast_sub hin.le]
  rw [hc]
  field_simp

lemma polyCap_mirror (hsym : ∀ t ∈ Θ, ω - t ∈ Θ) (K : Set ℝ²) :
    polyCap ω Θ (mirror ω '' K) = mirror ω '' polyCap ω Θ K := by
  ext p
  rw [mem_mirror_image]
  simp only [polyCap, mem_inter_iff, mem_iInter₂, mem_para_mirror]
  refine and_congr_right fun _ => ⟨fun h t ht => ?_, fun h t ht => ?_⟩
  · have := h (ω - t) (hsym t ht)
    rw [← mirror_mirror ω p, mirror_mem_QplusS_iff, sub_sub_cancel] at this
    exact this
  · have := h (ω - t) (hsym t ht)
    rw [← mirror_mirror ω p, mirror_mem_QplusS_iff]
    exact this

lemma polyNiche_mirror (hsym : ∀ t ∈ Θ, ω - t ∈ Θ) (K : Set ℝ²) :
    polyNiche ω Θ (mirror ω '' K) = mirror ω '' polyNiche ω Θ K := by
  ext p
  rw [mem_mirror_image]
  simp only [polyNiche, mem_inter_iff, mem_iUnion₂, exists_prop, mem_fan_mirror]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨t, ht, hQ⟩
    refine ⟨ω - t, hsym t ht, ?_⟩
    rw [← mirror_mirror ω p, mirror_mem_QminusS_iff] at hQ
    exact hQ
  · rintro ⟨t, ht, hQ⟩
    refine ⟨ω - t, hsym t ht, ?_⟩
    rw [← mirror_mirror ω p, mirror_mem_QminusS_iff, sub_sub_cancel]
    exact hQ

lemma polySofaArea_mirror (hsym : ∀ t ∈ Θ, ω - t ∈ Θ) (K : Set ℝ²) :
    polySofaArea ω Θ (mirror ω '' K) = polySofaArea ω Θ K := by
  rw [polySofaArea, polySofaArea, polyCap_mirror hsym, polyNiche_mirror hsym,
    volume_mirror_image, volume_mirror_image]

lemma isPolyCap_iff (hP : PolySetup ω Θ) (hK : IsCap K ω) :
    IsPolyCap ω Θ K ↔ polyCap ω Θ K = K := by
  constructor
  · intro h
    rw [polyCap_eq_capH hP hK, capH_supportFn hP h]
  · intro h
    refine ⟨hK, ?_⟩
    conv_lhs => rw [← h]
    rw [polyCap_eq_capH hP hK, capH_eq_iInter_polyCapAngles hP hK]

theorem IsPolyCap.image_mirror (hP : PolySetup ω Θ) (hsym : ∀ t ∈ Θ, ω - t ∈ Θ)
    (h : IsPolyCap ω Θ K) : IsPolyCap ω Θ (mirror ω '' K) := by
  rw [isPolyCap_iff hP h.1.image_mirror, polyCap_mirror hsym, (isPolyCap_iff hP h.1).1 h]

lemma mirror_oω (hω0 : 0 < ω) (hω1 : ω < π / 2) : mirror ω (oω ω) = oω ω := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  refine eq_of_inner_u_v_eq (t := 0) ?_ ?_
  · rw [inner_mirror_u, sub_zero, oω, inner_eq, inner_eq, pt_zero, pt_one, u_coord_zero,
      u_coord_one, u_coord_zero, u_coord_one, cos_add_pi_div_two, sin_add_pi_div_two,
      cos_zero, sin_zero]
    field_simp
    nlinarith [sin_sq_add_cos_sq ω]
  · rw [inner_mirror_v, oω, inner_eq, inner_eq, pt_zero, pt_one, v_coord_zero, v_coord_one,
      v_coord_zero, v_coord_one, show ω + π / 2 - 0 = ω + π / 2 by ring,
      cos_add_pi_div_two, sin_add_pi_div_two, cos_zero, sin_zero]
    field_simp
    nlinarith [sin_sq_add_cos_sq ω]

theorem IsMaxPolyCap.image_mirror (hP : PolySetup ω Θ) (hω1 : ω < π / 2)
    (hsym : ∀ t ∈ Θ, ω - t ∈ Θ) (h : IsMaxPolyCap ω Θ K) :
    IsMaxPolyCap ω Θ (mirror ω '' K) := by
  refine ⟨h.1.image_mirror hP hsym, ?_, ?_⟩
  · rw [mem_mirror_image, mirror_oω hP.pos hω1]
    exact h.2.1
  · intro K' hK'
    rw [polySofaArea_mirror hsym]
    calc polySofaArea ω Θ K' = polySofaArea ω Θ (mirror ω '' K') :=
          (polySofaArea_mirror hsym K').symm
      _ ≤ polySofaArea ω Θ K := h.2.2 _ (hK'.image_mirror hP hsym)

theorem IsBalancedMaxCap.image_mirror (hω0 : 0 < ω) (hω1 : ω < π / 2)
    (h : IsBalancedMaxCap K ω) : IsBalancedMaxCap (mirror ω '' K) ω := by
  obtain ⟨hcap, n, Ks, hmono, hn, hmax, hlim⟩ := h
  refine ⟨hcap.image_mirror, n, fun i => mirror ω '' Ks i, hmono, hn, fun i => ?_, ?_⟩
  · exact (hmax i).image_mirror (polySetup_uniform hω0 hω1.le (hn i).1) hω1
      (fun t ht => sub_mem_uniformAngles ht)
  · have hiso : Isometry (mirror ω) := by
      rw [← coe_mirrorL]; exact (mirrorL ω).isometry
    simpa only [Metric.hausdorffDist_image hiso] using hlim

end MirrorPoly

/-! ## Theorem 4.2.5 -/

section Thm425

variable {K : Set ℝ²}

/-- The key step of Theorem 4.2.5: if `r = (h_K(0), r_y)` lies on the line `l_K(ω)` and
`g² + r_y² = 1`, then `g ≤ w°_K`. -/
theorem le_gapWinf_of_sq (hω0 : 0 < ω) (hω1 : ω < π / 2) (hK : IsCap K ω)
    {g ry : ℝ} (_hg0 : 0 ≤ g) (hsq : g ^ 2 + ry ^ 2 = 1)
    (hr : ⟪pt (supportFn K 0) ry, u ω⟫ = 1) : g ≤ gapWinf K ω := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  refine le_csInf ⟨gapW K (ω / 2), ⟨ω / 2, ⟨by linarith, by linarith⟩, rfl⟩⟩ ?_
  rintro x ⟨t, ht, rfl⟩
  have hct : 0 < cos t :=
    cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  set r : ℝ² := pt (supportFn K 0) ry with hrdef
  have hr0 : ⟪r, u 0⟫ = supportFn K 0 := by
    rw [hrdef, inner_u_decomp, pt_zero, pt_one, cos_zero, sin_zero]; ring
  have hrt : ⟪r, u t⟫ = supportFn K 0 * cos t + ry * sin t := by
    rw [hrdef, inner_u_decomp, pt_zero, pt_one]
  have hbnd : supportFn K t ≤ ⟪r, u t⟫ := by
    rw [supportFn_le_iff hK.isCompact hK.nonempty]
    intro p hp
    rw [inner_u_decomp_cone hsω.ne' p t, inner_u_decomp_cone hsω.ne' r t, hr0, hr]
    have hα : 0 ≤ sin (ω - t) / sin ω :=
      div_nonneg (sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.2]) (by linarith [ht.1, pi_pos]))
        hsω.le
    have hβ : 0 ≤ sin t / sin ω := div_nonneg hst.le hsω.le
    have h1 : ⟪p, u 0⟫ ≤ supportFn K 0 := le_supportFn hK.isCompact hp 0
    have h2 : ⟪p, u ω⟫ ≤ 1 := by
      rw [← hK.supportFn_ω]; exact le_supportFn hK.isCompact hp ω
    nlinarith
  rw [hrt] at hbnd
  have hcs : g * cos t + ry * sin t ≤ 1 := by
    nlinarith [sq_nonneg (g * sin t - ry * cos t), sin_sq_add_cos_sq t]
  have hfinal : (supportFn K t - 1) / cos t ≤ supportFn K 0 - g := by
    rw [div_le_iff₀ hct]
    nlinarith
  rw [gapW]
  linarith

/-- The triangle `Δ_ω` with vertices `O`, `o_ω − v₀ = c_ω u₀` and `o_ω − u_ω = c_ω v_ω`. -/
def triangleD (ω : ℝ) : Set ℝ² := convexHull ℝ {0, cw ω • u 0, cw ω • v ω}

set_option maxHeartbeats 1000000 in
/-- **Theorem 4.2.5**, right-hand case: if `h_K(0) ≥ d_{ω,min} + c_ω` then the three vertices of
`Δ_ω` lie in the closed quadrant `Q⁻_K(t)` for `t = π/2 − ω`. -/
theorem wedge_right (hω0 : 0 < ω) (hω1 : ω < π / 2) (hcos : cos ω ≤ 5 / 11)
    (hK : IsBalancedMaxCap K ω) (hd : dmin ω + cw ω ≤ supportFn K 0) :
    ∀ p ∈ ({0, cw ω • u 0, cw ω • v ω} : Set ℝ²),
      ⟪p, u (π / 2 - ω)⟫ ≤ supportFn K (π / 2 - ω) - 1 ∧
      ⟪p, u (π / 2 - ω + π / 2)⟫ ≤ supportFn K (π / 2 - ω + π / 2) - 1 := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  have hpy := sin_sq_add_cos_sq ω
  have hs1 : sin ω ≤ 1 := sin_le_one ω
  have hcap : IsCap K ω := hK.1
  have hcw0 : 0 ≤ cw ω := cw_nonneg hω0 hω1
  have hcwc : cw ω * cos ω = 1 - sin ω := by rw [cw]; field_simp
  have hd1 := one_le_dmin ω
  have hq0 : pt (supportFn K 0) 0 ∈ K := by
    have hmem := hcap.cornerA_mem hω0 hω1.le
    rwa [hcap.cornerA_eq] at hmem
  have hK0le : supportFn K 0 ≤ 1 / cos ω := by
    rw [supportFn_le_iff hcap.isCompact hcap.nonempty]
    intro p hp
    obtain ⟨⟨hy0, hy1⟩, -, hq1⟩ := mem_para_iff.1 (hcap.subset_para hp)
    rw [inner_u_decomp] at hq1 ⊢
    rw [cos_zero, sin_zero, mul_one, mul_zero, add_zero, le_div_iff₀ hcω]
    nlinarith
  rw [le_div_iff₀ hcω] at hK0le
  obtain ⟨ry, hrydef⟩ : ∃ ry : ℝ, ry = (1 - supportFn K 0 * cos ω) / sin ω := ⟨_, rfl⟩
  have hrys : ry * sin ω = 1 - supportFn K 0 * cos ω := by rw [hrydef]; field_simp
  have hry0 : 0 ≤ ry := by rw [hrydef]; exact div_nonneg (by linarith) hsω.le
  have hry1 : ry ≤ 1 := by
    rw [hrydef, div_le_one hsω]
    have hcwle : cw ω ≤ supportFn K 0 := by linarith
    rw [cw, div_le_iff₀ hcω] at hcwle
    linarith
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ, g = Real.sqrt (1 - ry ^ 2) := ⟨_, rfl⟩
  have hg0 : 0 ≤ g := by rw [hgdef]; exact Real.sqrt_nonneg _
  have hgsq : g ^ 2 = 1 - ry ^ 2 := by
    rw [hgdef]; exact Real.sq_sqrt (by nlinarith only [hry0, hry1])
  have hrω : ⟪pt (supportFn K 0) ry, u ω⟫ = 1 := by
    rw [inner_u_decomp, pt_zero, pt_one, hrydef]
    field_simp
    ring
  have hgw : g ≤ gapWinf K ω :=
    le_gapWinf_of_sq hω0 hω1 hcap hg0 (by nlinarith only [hgsq]) hrω
  have hq1 : pt (cw ω - g) 1 ∈ K := hK.mem_top_segment hω0 hω1 hg0 hgw
  -- `g ≥ 2 cos ω`
  have hg2c : 2 * cos ω ≤ g := by
    have hdm := dmin_mul_cos_le_sin hω0 hω1 hcos
    have hineq := dmin_ineq hω0 hω1 hcos
    have hle : ry * sin ω ≤ sin ω - dmin ω * cos ω := by
      rw [hrys]
      linarith only [mul_le_mul_of_nonneg_right hd hcω.le, hcwc]
    have hnn : 0 ≤ ry * sin ω := mul_nonneg hry0 hsω.le
    have hsq2 : (ry * sin ω) ^ 2 ≤ (sin ω - dmin ω * cos ω) ^ 2 := by
      nlinarith only [hle, hnn]
    have hstep : 4 * cos ω ^ 2 * sin ω ^ 2 < sin ω ^ 2 - (sin ω - dmin ω * cos ω) ^ 2 := by
      nlinarith only [mul_lt_mul_of_pos_left hineq hcω]
    have hmul : g ^ 2 * sin ω ^ 2 = sin ω ^ 2 - (ry * sin ω) ^ 2 := by rw [hgsq]; ring
    have hpos : 0 < sin ω ^ 2 := by positivity
    have hgg : 4 * cos ω ^ 2 < g ^ 2 := by nlinarith only [hmul, hsq2, hstep, hpos]
    nlinarith only [hgg, hg0, hcω]
  -- the two key inequalities
  have hA : cw ω * sin ω ≤ supportFn K (π / 2 - ω) - 1 := by
    have hle := le_supportFn hcap.isCompact hq0 (π / 2 - ω)
    rw [inner_u_decomp, pt_zero, pt_one, cos_pi_div_two_sub] at hle
    have hdsin : 1 < dmin ω * sin ω := one_lt_dmin_mul_sin hω0 hω1 hcos
    linarith only [hle, hdsin, mul_le_mul_of_nonneg_right hd hsω.le]
  have hB : cw ω * sin (2 * ω) ≤ supportFn K (π / 2 - ω + π / 2) - 1 := by
    have hle := le_supportFn hcap.isCompact hq1 (π / 2 - ω + π / 2)
    rw [inner_u_decomp, pt_zero, pt_one, show π / 2 - ω + π / 2 = π - ω by ring,
      cos_pi_sub, sin_pi_sub] at hle
    have hexp : (cw ω - g) * -cos ω + 1 * sin ω = -(1 - sin ω) + g * cos ω + sin ω := by
      rw [← hcwc]; ring
    rw [hexp] at hle
    rw [show π / 2 - ω + π / 2 = π - ω by ring, sin_two_mul]
    have hlhs : cw ω * (2 * sin ω * cos ω) = 2 * sin ω * (1 - sin ω) := by rw [← hcwc]; ring
    rw [hlhs]
    have hgc : 2 * cos ω * cos ω ≤ g * cos ω := mul_le_mul_of_nonneg_right hg2c hcω.le
    linarith only [hle, hgc, hpy]
  have hA0 : 0 ≤ supportFn K (π / 2 - ω) - 1 := le_trans (mul_nonneg hcw0 hsω.le) hA
  have hsin2 : 0 ≤ sin (2 * ω) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
  have hB0 : 0 ≤ supportFn K (π / 2 - ω + π / 2) - 1 :=
    le_trans (mul_nonneg hcw0 hsin2) hB
  have hcos2 : cw ω * cos (2 * ω) ≤ 0 := by
    have h2 : cos (2 * ω) ≤ 0 := by rw [cos_two_mul]; nlinarith only [hcos, hcω]
    exact mul_nonpos_of_nonneg_of_nonpos hcw0 h2
  rintro p (rfl | rfl | rfl)
  · exact ⟨by rw [inner_zero_left]; exact hA0, by rw [inner_zero_left]; exact hB0⟩
  · refine ⟨?_, ?_⟩
    · rw [real_inner_smul_left, inner_u_u_eq_cos, show (0 : ℝ) - (π / 2 - ω) = ω - π / 2 by ring,
        cos_sub_pi_div_two]
      exact hA
    · rw [real_inner_smul_left, inner_u_u_eq_cos,
        show (0 : ℝ) - (π / 2 - ω + π / 2) = ω - π by ring, cos_sub_pi]
      linarith only [hB0, hcwc, hs1]
  · refine ⟨?_, ?_⟩
    · rw [← u_add_pi_div_two, real_inner_smul_left, inner_u_u_eq_cos,
        show ω + π / 2 - (π / 2 - ω) = 2 * ω by ring]
      linarith only [hA0, hcos2]
    · rw [← u_add_pi_div_two, real_inner_smul_left, inner_u_u_eq_cos,
        show ω + π / 2 - (π / 2 - ω + π / 2) = 2 * ω - π / 2 by ring, cos_sub_pi_div_two]
      exact hB

lemma mirror_zero (ω : ℝ) : mirror ω (0 : ℝ²) = 0 := by
  rw [← coe_mirrorL]; exact (mirrorL ω).map_zero

lemma pi_div_four_lt (hω0 : 0 < ω) (hcos : cos ω ≤ 5 / 11) : π / 4 < ω := by
  by_contra hcon
  push Not at hcon
  have h1 : cos (π / 4) ≤ cos ω :=
    cos_le_cos_of_nonneg_of_le_pi hω0.le (by linarith [pi_pos]) hcon
  rw [cos_pi_div_four] at h1
  have h2 : (1 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  linarith

set_option maxHeartbeats 1000000 in
/-- **Theorem 4.2.5.** For a balanced maximum cap of area `≥ 2.2` with `ω ∈ [arccos(5/11), π/2)`,
the three vertices of `Δ_ω` lie in a closed quadrant `Q⁻_K(t)` with `t ∈ (0, ω)`. -/
theorem exists_wedge (hω0 : 0 < ω) (hω1 : ω < π / 2) (hcos : cos ω ≤ 5 / 11)
    (hK : IsBalancedMaxCap K ω) (harea : 11 / 5 ≤ volume.real K) :
    ∃ t ∈ Ioo (0 : ℝ) ω, ∀ p ∈ ({0, cw ω • u 0, cw ω • v ω} : Set ℝ²),
      ⟪p, u t⟫ ≤ supportFn K t - 1 ∧ ⟪p, u (t + π / 2)⟫ ≤ supportFn K (t + π / 2) - 1 := by
  have hpi4 : π / 4 < ω := pi_div_four_lt hω0 hcos
  have hpi := pi_pos
  rcases le_or_gt (dmin ω + cw ω) (supportFn K 0) with hcase | hcase
  · refine ⟨π / 2 - ω, ⟨by linarith, by linarith⟩, ?_⟩
    exact wedge_right hω0 hω1 hcos hK hcase
  · -- the mirror case
    have hleft : dmin ω + cw ω ≤ supportFn K (ω + π / 2) := by
      by_contra hcon
      push Not at hcon
      exact absurd (measureReal_lt_of_supportFn_lt hω0 hω1 hcos hK.1 hcase hcon) (not_lt.2 harea)
    have hMK : IsBalancedMaxCap (mirror ω '' K) ω := hK.image_mirror hω0 hω1
    have hMs : dmin ω + cw ω ≤ supportFn (mirror ω '' K) 0 := by
      rw [supportFn_mirror, sub_zero]; exact hleft
    have hW := wedge_right hω0 hω1 hcos hMK hMs
    refine ⟨2 * ω - π / 2, ⟨by linarith, by linarith⟩, ?_⟩
    intro q hq
    have hmq : mirror ω q ∈ ({0, cw ω • u 0, cw ω • v ω} : Set ℝ²) := by
      rcases hq with rfl | rfl | rfl
      · rw [mirror_zero]; exact Or.inl rfl
      · rw [mirror_smul, mirror_u_zero]; exact Or.inr (Or.inr rfl)
      · rw [mirror_smul, mirror_v]; exact Or.inr (Or.inl rfl)
    obtain ⟨h1, h2⟩ := hW _ hmq
    rw [supportFn_mirror] at h1
    rw [supportFn_mirror] at h2
    constructor
    · have he : ⟪q, u (2 * ω - π / 2)⟫ = ⟪mirror ω q, u (π / 2 - ω + π / 2)⟫ := by
        rw [inner_mirror_u]
        congr 2
        ring
      rw [he]
      rw [show ω + π / 2 - (π / 2 - ω + π / 2) = 2 * ω - π / 2 by ring] at h2
      exact h2
    · have he : ⟪q, u (2 * ω - π / 2 + π / 2)⟫ = ⟪mirror ω q, u (π / 2 - ω)⟫ := by
        rw [inner_mirror_u]
        congr 2
        ring
      rw [he]
      rw [show ω + π / 2 - (π / 2 - ω) = 2 * ω - π / 2 + π / 2 by ring] at h1
      exact h1

end Thm425

end Sofa
