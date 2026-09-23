/-
# Sofa/GerverNiche.lean — Theorem 8.4.1 (2): the niche of Gerver's sofa

For the cap `K = C(G)` of the upstream Gerver sofa the niche is
`N(K) = {y ≥ 0} ∩ ⋃_{s ∈ (0, π/2)} Q⁻(s)` with `Q⁻(s) = {ca s < 0, cb s < 0}` (`mem_niche_Kg`).
This file proves the statements of Baek's Theorem 8.4.1 (2) that the proof of the main theorem
uses (the fields of `GerverNicheFacts` in `Sofa/Main.lean`):

* the tails `B|(π/2 − θ, π/2)`, `D|(0, θ)` and the core `x_K|[φ, π/2 − φ]` lie in the closure of
  `N(K)` (`Bg_mem_closure`, `Dg_mem_closure`, `innerCorner_mem_closure`): each is on the boundary
  of its own quadrant (`F > 0`) and at height `≥ 0` (`> 0` for the core);
* the tails are not in `N(K)` (`Bg_not_mem_niche`, `Dg_not_mem_niche`): no inner quadrant reaches
  the arch (`Sofa/GerverArch.lean`);
* every point `q ∈ N(K)` lies strictly below a point of the arch with the same `x`-coordinate
  (`niche_below`): the arch is a continuous curve over `[x(D(0)), x(B(π/2))]` (intermediate value
  theorem), no inner quadrant reaches the `x`-axis outside this interval, and a point of the arch
  above `q` would lie in the quadrant `Q⁻(s)` of `q` (quadrants are closed downwards).

STATUS: [PROOF-C] [AXIOM-CHECK] round 41 (2026-09-23, Opus 5.5), no `sorry`.
-/
import Sofa.GerverArch

noncomputable section

open Real Set MeasureTheory MovingSofa Filter Topology
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa.GP

open GC IA
open MovingSofa.GerversSofa (A B φ θ r)

/-! ## The niche of `K = C(G)` -/

/-- **The niche of `C(G)`**: `q ∈ N(K)` iff `q` lies above the `x`-axis and in some inner
quadrant `Q⁻(s)`, `0 < s < π/2`. -/
lemma mem_niche_Kg {q : ℝ²} :
    q ∈ niche Kg (π / 2) ↔ 0 ≤ q 1 ∧ ∃ s ∈ Ioo (0 : ℝ) (π / 2), ca s q < 0 ∧ cb s q < 0 := by
  rw [mem_niche_iff]
  have hfan : q ∈ fan (π / 2) ↔ 0 ≤ q 1 := by
    simp only [fan, mem_ofPred_eq, inner_u_pi_div_two, and_self]
  rw [hfan]
  refine and_congr Iff.rfl (exists_congr fun s => and_congr_right fun hs => ?_)
  rw [mem_QminusS_iff, supportFn_Kg ⟨hs.1.le, hs.2.le⟩, supportFn_Kg' ⟨hs.1.le, hs.2.le⟩,
    u_add_pi_div_two, ca, cb]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

lemma not_mem_niche_of {z : ℝ²} (h : ∀ s ∈ Ioo (0 : ℝ) (π / 2), ¬(ca s z < 0 ∧ cb s z < 0)) :
    z ∉ niche Kg (π / 2) := by
  rw [mem_niche_Kg]
  rintro ⟨-, s, hs, h1, h2⟩
  exact h s hs ⟨h1, h2⟩

/-- **The tail `B` is not in the niche.** -/
theorem Bg_not_mem_niche {t : ℝ} (ht : t ∈ Ioo (π / 2 - θ) (π / 2)) :
    Bg t ∉ niche Kg (π / 2) :=
  not_mem_niche_of fun _ hs => Bg_not_mem ⟨ht.1.le, ht.2.le⟩ hs

/-- **The tail `D` is not in the niche.** -/
theorem Dg_not_mem_niche {t : ℝ} (ht : t ∈ Ioo 0 θ) : Dg t ∉ niche Kg (π / 2) :=
  not_mem_niche_of fun _ hs => Dg_not_mem ⟨ht.1.le, ht.2.le⟩ hs

/-! ## Heights -/

lemma hasDerivAt_coord {γ : ℝ → ℝ²} {γ' : ℝ²} {τ : ℝ} (h : HasDerivAt γ γ' τ) (i : Fin 2) :
    HasDerivAt (fun τ => γ τ i) (γ' i) τ :=
  (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt τ h

lemma continuous_coord {γ : ℝ → ℝ²} (hγ : Continuous γ) (i : Fin 2) :
    Continuous fun τ => γ τ i :=
  (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).continuous.comp hγ

/-- The tail `D` lies above the `x`-axis: `D_y(0) = 0` and `D_y' = (1 − r) sin ≥ 0`. -/
lemma Dg_coord1_nonneg {t : ℝ} (ht : t ∈ Icc 0 θ) : 0 ≤ Dg t 1 := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  have hθ := θ_lt_sR
  have hsign : ∀ τ ∈ Ioo 0 t, τ ∉ brkSet → 0 ≤ (1 - r τ) * sin τ := by
    intro τ hτ _
    have h1 : 0 ≤ 1 - r τ := by linarith [r_le_one (hτ.2.le.trans (ht.2.trans hθ.le))]
    exact mul_nonneg h1 (sin_nonneg_of_nonneg_of_le_pi hτ.1.le (by linarith [hτ.2, ht.2]))
  have hmono := monotoneOn_of_hasDerivAt_nonneg_off_countable
    (f := fun τ => Dg τ 1) (f' := fun τ => (1 - r τ) * sin τ) brkSet_countable
    (continuous_coord continuous_Dg 1).continuousOn
    (fun τ _ hτ => by
      have h := hasDerivAt_coord (hasDerivAt_Dg (continuousAt_r_of_not_mem hτ)) 1
      simpa only [PiLp.smul_apply, smul_eq_mul, u_coord_one] using h)
    (intervalIntegrable_one_sub_r_mul continuous_sin _ _) hsign
  have := hmono ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩ ht.1
  simpa only [Dg_zero_coord1] using this

/-- The tail `B` lies above the `x`-axis (mirror image). -/
lemma Bg_coord1_nonneg {t : ℝ} (ht : t ∈ Icc (π / 2 - θ) (π / 2)) : 0 ≤ Bg t 1 := by
  rw [← refl_Dg, refl_coord_one]
  exact Dg_coord1_nonneg ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- The core lies strictly above the `x`-axis: `τ ↦ x_K(τ)_y` is quasi-concave on
`[φ, π/2 − φ]` and positive at the two ends. -/
lemma xKg_coord1_pos {t : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) : 0 < xKg t 1 := by
  obtain ⟨p1, p2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  obtain ⟨ha, hb, hs1, hs0, hc0, hc1⟩ := JL_bounds
  obtain ⟨x01, x02⟩ := x0_bounds
  -- the right end `J_L`
  have hJL : 0 < xKg (π / 2 - φ) 1 := by
    simp only [xKg, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, u_coord_one, v_coord_one,
      sin_pi_div_two_sub, cos_pi_div_two_sub]
    have hsφ : 39 / 1000 - (4 / 100) ^ 3 / 6 ≤ sin φ := by
      have := sin_gt_sub_cube (x := φ) (by linarith)
      have : φ ^ 3 ≤ (4 / 100) ^ 3 := by
        exact pow_le_pow_left₀ (by linarith) (by linarith) 3
      linarith
    have hφ2 : φ ^ 2 ≤ 16 / 10000 := by nlinarith
    have hp1 : -(1 / 1000) ≤ p₁ (π / 2 - φ) := by
      rw [p₁_JL]
      have := one_sub_sq_div_two_le_cos (x := φ)
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ GerversSofa.x 0) hs0
      nlinarith
    nlinarith [mul_le_mul hb hsφ (by norm_num) (by linarith),
      mul_nonneg (by linarith : (0 : ℝ) ≤ p₁ (π / 2 - φ) + 1 / 1000) (by linarith : (0 : ℝ) ≤ cos φ)]
  -- the left end `J_R` has the same height
  have hJR : xKg φ 1 = xKg (π / 2 - φ) 1 := by
    rw [xKg_phi_refl, refl_coord_one, Dg_theta]
  have hω : ∀ τ ∈ Ioo φ (π / 2 - φ), 0 < cos τ := fun τ hτ =>
    cos_pos_of_mem_Ioo ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hd : ∀ τ ∈ Ioo φ (π / 2 - φ), HasDerivAt (fun τ => xKg τ 1)
      (cos τ * (Gr τ - Fr τ * tan τ)) τ := by
    intro τ hτ
    have hc := (hω τ hτ).ne'
    have h := hasDerivAt_coord (hasDerivAt_xKg τ) 1
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, u_coord_one, v_coord_one] at h
    refine h.congr_deriv ?_
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    ring
  have hk : ∀ x ∈ Ioo φ (π / 2 - φ), ∀ y ∈ Ioo φ (π / 2 - φ), x ≤ y →
      Gr x - Fr x * tan x < 0 → Gr y - Fr y * tan y ≤ 0 := by
    intro x hx y hy hxy hkx
    have hxc : x ∈ Icc φ (π / 2 - φ) := ⟨hx.1.le, hx.2.le⟩
    have hyc : y ∈ Icc φ (π / 2 - φ) := ⟨hy.1.le, hy.2.le⟩
    have h1 : Gr y ≤ Gr x := antitoneOn_Gr hxc hyc hxy
    have h2 : Fr x ≤ Fr y := monotoneOn_Fr hxc hyc hxy
    have h3 : tan x ≤ tan y :=
      strictMonoOn_tan.monotoneOn ⟨by linarith [hx.1], by linarith [hx.2]⟩
        ⟨by linarith [hy.1], by linarith [hy.2]⟩ hxy
    have h4 : 0 ≤ tan x :=
      tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith [hx.1]) (by linarith [hx.2])
    have := mul_le_mul h2 h3 h4 ((Fr_ge_A hyc).trans' A_pos.le)
    linarith
  have hmin := min_le_of_hasDerivAt_mul (continuous_coord continuous_xKg 1).continuousOn
    hd hω hk t ht
  have hend : 0 < min (xKg φ 1) (xKg (π / 2 - φ) 1) := by
    rw [hJR, min_self]; exact hJL
  exact lt_of_lt_of_le hend hmin

/-! ## The arch is in the closure of the niche -/

lemma inner_add_u_v_u (t : ℝ) : ⟪u t + v t, u t⟫ = 1 := by
  rw [inner_add_left, inner_u_u, inner_v_u, add_zero]

lemma inner_add_u_v_v (t : ℝ) : ⟪u t + v t, v t⟫ = 1 := by
  rw [inner_add_left, inner_u_v, inner_v_v, zero_add]

lemma ca_sub_smul (s : ℝ) (z w : ℝ²) (δ : ℝ) : ca s (z - δ • w) = ca s z - δ * ⟪w, u s⟫ := by
  rw [ca, ca, inner_sub_left, real_inner_smul_left]; ring

lemma cb_sub_smul (s : ℝ) (z w : ℝ²) (δ : ℝ) : cb s (z - δ • w) = cb s z - δ * ⟪w, v s⟫ := by
  rw [cb, cb, inner_sub_left, real_inner_smul_left]; ring

lemma norm_u_add_v_le (t : ℝ) : ‖u t + v t‖ ≤ 2 := by
  have h1 := norm_add_le (u t) (v t)
  have h2 : ‖v t‖ = 1 := by
    rw [← u_add_pi_div_two, norm_u]
  rw [norm_u, h2] at h1
  linarith

lemma norm_u_zero : ‖u 0‖ = 1 := norm_u 0

/-- **The core lies in the closure of the niche**: `x_K(t) − δ(u_t + v_t) ∈ N(K)`. -/
theorem innerCorner_mem_closure {t : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) :
    innerCorner Kg t ∈ closure (niche Kg (π / 2)) := by
  obtain ⟨p1, p2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  have ht' : t ∈ Icc (0 : ℝ) (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rw [innerCorner_Kg_eq ht', Metric.mem_closure_iff]
  intro ε hε
  have hy := xKg_coord1_pos ht
  set δ := min (ε / 4) (xKg t 1 / 4) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ ε / 4 := min_le_left _ _
  have hδ2 : δ ≤ xKg t 1 / 4 := min_le_right _ _
  refine ⟨xKg t - δ • (u t + v t), mem_niche_Kg.2 ⟨?_, t, ⟨by linarith [ht.1], by linarith [ht.2]⟩,
    ?_, ?_⟩, ?_⟩
  · have hst := sin_le_one t
    have hct := cos_le_one t
    have hs0 := sin_nonneg_of_nonneg_of_le_pi (x := t) (by linarith [ht.1]) (by linarith [ht.2])
    have hc0 := cos_nonneg_of_mem_Icc (x := t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, u_coord_one,
      v_coord_one]
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add hst hct) hδ0.le]
  · rw [ca_sub_smul, ca_xKg_self, inner_add_u_v_u]; linarith
  · rw [cb_sub_smul, cb_xKg_self, inner_add_u_v_v]; linarith
  · rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_of_nonneg hδ0.le]
    have := norm_u_add_v_le t
    nlinarith

/-- **The tail `D` lies in the closure of the niche**: `D(t) + δ e₀ ∈ N(K)`. -/
theorem Dg_mem_closure {t : ℝ} (ht : t ∈ Ioo 0 θ) : Dg t ∈ closure (niche Kg (π / 2)) := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- `G(t) = F(π/2 − t) > 0`
  have hG : 0 < Gr t := by
    rw [Gr_eq]; exact F_pos ⟨by linarith [ht.2], by linarith [ht.1]⟩
  set δ := min (ε / 2) (Gr t / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ ε / 2 := min_le_left _ _
  have hδ2 : δ ≤ Gr t / 2 := min_le_right _ _
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2])
  have hc1 : cos t ≤ 1 := cos_le_one t
  refine ⟨Dg t - (-δ) • u 0, mem_niche_Kg.2 ⟨?_, t, ⟨ht.1, by linarith [ht.2]⟩, ?_, ?_⟩, ?_⟩
  · have := Dg_coord1_nonneg ⟨ht.1.le, ht.2.le⟩
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, u_coord_one, sin_zero]
    linarith
  · rw [ca_sub_smul, ca_Dg_self, inner_u_u_sub, sub_zero]
    nlinarith [mul_le_mul_of_nonneg_left hc1 hδ0.le]
  · rw [cb_sub_smul, cb_Dg_self, inner_u_v_eq_neg_sin, sub_zero]
    nlinarith [mul_pos hδ0 hs]
  · rw [dist_eq_norm, sub_sub_cancel, norm_smul, norm_u_zero, mul_one, Real.norm_eq_abs,
      abs_neg, abs_of_pos hδ0]
    linarith

/-- **The tail `B` lies in the closure of the niche**: `B(t) − δ e₀ ∈ N(K)`. -/
theorem Bg_mem_closure {t : ℝ} (ht : t ∈ Ioo (π / 2 - θ) (π / 2)) :
    Bg t ∈ closure (niche Kg (π / 2)) := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hF : 0 < Fr t := F_pos ⟨by linarith [ht.1], ht.2⟩
  set δ := min (ε / 2) (Fr t / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ ε / 2 := min_le_left _ _
  have hδ2 : δ ≤ Fr t / 2 := min_le_right _ _
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1], ht.2⟩
  have hs1 : sin t ≤ 1 := sin_le_one t
  refine ⟨Bg t - δ • u 0, mem_niche_Kg.2 ⟨?_, t, ⟨by linarith [ht.1], ht.2⟩, ?_, ?_⟩, ?_⟩
  · have := Bg_coord1_nonneg ⟨ht.1.le, ht.2.le⟩
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, u_coord_one, sin_zero]
    linarith
  · rw [ca_sub_smul, ca_Bg_self, inner_u_u_sub, sub_zero]
    nlinarith [mul_pos hδ0 hc]
  · rw [cb_sub_smul, cb_Bg_self, inner_u_v_eq_neg_sin, sub_zero]
    nlinarith [mul_le_mul_of_nonneg_left hs1 hδ0.le]
  · rw [dist_eq_norm, sub_sub_cancel, norm_smul, norm_u_zero, mul_one, Real.norm_of_nonneg hδ0.le]
    linarith

/-! ## The niche lies below the arch -/

lemma Bg_half_coord1 : Bg (π / 2) 1 = 0 := by
  rw [← refl_Dg, refl_coord_one, sub_self, Dg_zero_coord1]

/-- **Every point of the niche lies strictly below a point of the arch** with the same
`x`-coordinate. -/
theorem niche_below {q : ℝ²} (hq : q ∈ niche Kg (π / 2)) :
    (∃ t ∈ Icc 0 θ, Dg t 0 = q 0 ∧ q 1 < Dg t 1) ∨
    (∃ t ∈ Icc φ (π / 2 - φ), innerCorner Kg t 0 = q 0 ∧ q 1 < innerCorner Kg t 1) ∨
    (∃ t ∈ Icc (π / 2 - θ) (π / 2), Bg t 0 = q 0 ∧ q 1 < Bg t 1) := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  obtain ⟨hq1, s, hs, h1, h2⟩ := mem_niche_Kg.1 hq
  have hs0 : 0 < sin s := sin_pos_of_pos_of_lt_pi hs.1 (by linarith [hs.2])
  have hc0 : 0 < cos s := cos_pos_of_mem_Ioo ⟨by linarith [hs.1], hs.2⟩
  -- a point of the arch above `q` outside `Q⁻(s)` is strictly above `q`
  have above : ∀ P : ℝ², P 0 = q 0 → ¬(ca s P < 0 ∧ cb s P < 0) → q 1 < P 1 := by
    intro P hP hPn
    by_contra hle
    push Not at hle
    apply hPn
    rw [ca_eq, hP] at ⊢
    rw [cb_eq, hP] at ⊢
    rw [ca_eq] at h1
    rw [cb_eq] at h2
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hle hs0.le]
    · nlinarith [mul_le_mul_of_nonneg_right hle hc0.le]
  -- the `x`-range of the niche
  have hL : Dg 0 0 ≤ q 0 := by
    by_contra hlt
    push Not at hlt
    have k := cb_Dg_zero_nonneg ⟨hs.1.le, hs.2.le⟩
    rw [cb_eq, Dg_zero_coord1] at k
    rw [cb_eq] at h2
    nlinarith [mul_lt_mul_of_pos_right hlt hs0, mul_nonneg hq1 hc0.le]
  have hR : q 0 ≤ Bg (π / 2) 0 := by
    by_contra hlt
    push Not at hlt
    have k := ca_Bg_half_nonneg ⟨hs.1.le, hs.2.le⟩
    rw [ca_eq, Bg_half_coord1] at k
    rw [ca_eq] at h1
    nlinarith [mul_lt_mul_of_pos_right hlt hc0, mul_nonneg hq1 hs0.le]
  rcases le_total (q 0) (Dg θ 0) with hD | hD
  · obtain ⟨t, ht, hte⟩ := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ θ)
      (continuous_coord continuous_Dg 0).continuousOn ⟨hL, hD⟩
    exact Or.inl ⟨t, ht, hte, above _ hte (Dg_not_mem ht hs)⟩
  rcases le_total (q 0) (xKg φ 0) with hX | hX
  · have hD' : xKg (π / 2 - φ) 0 ≤ q 0 := by rw [← Dg_theta]; exact hD
    obtain ⟨t, ht, hte⟩ := intermediate_value_Icc' φ_le_half_sub
      (continuous_coord continuous_xKg 0).continuousOn ⟨hD', hX⟩
    have ht' : t ∈ Icc (0 : ℝ) (π / 2) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine Or.inr (Or.inl ⟨t, ht, ?_, ?_⟩)
    · rw [innerCorner_Kg_eq ht']; exact hte
    · rw [innerCorner_Kg_eq ht']; exact above _ hte (xKg_not_mem ht hs)
  · have hB' : Bg (π / 2 - θ) 0 ≤ q 0 := by rw [Bg_start']; exact hX
    obtain ⟨t, ht, hte⟩ := intermediate_value_Icc (by linarith : π / 2 - θ ≤ π / 2)
      (continuous_coord continuous_Bg 0).continuousOn ⟨hB', hR⟩
    exact Or.inr (Or.inr ⟨t, ht, hte, above _ hte (Bg_not_mem ht hs)⟩)

end Sofa.GP
