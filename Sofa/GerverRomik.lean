/-
# Sofa/GerverRomik.lean — Romik's ODEs for Gerver's sofa (Thm 8.4.1 (1) + Thm 8.4.2)

For the cap `K = C(G)` of the upstream `G = gerversSofa` (`Sofa/GerverCap.lean`):

* **vertex curves**: away from the break points, `v⁺_K(t) = A(t)` and `v⁺_K(t + π/2) = C(t)`
  (`vtxP_Kg`, `vtxP_Kg_add`): the support function `h_K = p₁ + 1` is differentiable there and
  `edgeMax K t` is its right derivative;
* **derivatives**: `A' = r(π/2 − t) v_t`, `C' = −r(t) u_t`,
  `x_K' = (p₁' − p₂) u_t + (p₁ + p₂') v_t`, and `p₁'' = r(π/2 − t) − p₁ − 1`,
  `p₂'' = r(t) − p₂ − 1`;
* **the tails** `B = p₁ u + p₁' v`, `D = −p₂' u + p₂ v` (the envelopes of the inner walls
  `ca = 0`, `cb = 0`): `B' = (r(π/2 − t) − 1) v_t`, `D' = (1 − r(t)) u_t`;
* **Romik's identities** (`F_piece1`, `F_piece2`, `F_piece3`): for
  `F(t) = p₂(t) − p₁'(t) = [y(t) − y(π/2 − t)] cos t + [x(t) + x(π/2 − t) + 2 − 4x₀] sin t − 1`,
  `F = A + t − φ` on `[φ, π/2 − θ]` and `F = r` on `[π/2 − θ, π/2 − φ]`: with the closed forms of
  `x`, `y` (`Sofa/GerverClosed.lean`) these are `linear_combination`s of Romik's equations `E₂`, `E₄`
  (found with sympy);
* hence **Romik's ten ODEs** (`gerverODE_Kg : GerverODE φ θ K B D`).

STATUS: [PROOF-C] round 39 (2026-09-23, Opus 5.5).
-/
import Sofa.GerverCap
import Sofa.GerverODE

noncomputable section

open Real Set MeasureTheory intervalIntegral MovingSofa Filter Topology
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa.GP

open GC IA
open MovingSofa.GerversSofa (A B φ θ r)

/-! ## `r` away from the break points -/

lemma continuousAt_r {k : ℕ} (hk : k ≤ 3) {t : ℝ} (ht : t ∈ Ioo (brk k) (brk (k + 1))) :
    ContinuousAt r t := by
  have hev : r =ᶠ[𝓝 t] fun s => ra k + rb k * s + rc k * s ^ 2 := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact r_eq_quad hk ⟨hs.1, hs.2.le⟩
  exact (continuousAt_congr hev).2 (by fun_prop)

lemma continuousAt_r_top {t : ℝ} (ht : π / 2 - φ < t) : ContinuousAt r t := by
  have hev : r =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact r_zero hs
  exact (continuousAt_congr hev).2 continuousAt_const

/-- The angles of `(0, π/2)` away from the break points: an open set, symmetric under
`t ↦ π/2 − t`. -/
def good : Set ℝ := Ioo 0 (π / 2) \ {φ, θ, π / 2 - θ, π / 2 - φ}

lemma isOpen_good : IsOpen good :=
  isOpen_Ioo.sdiff ((((Set.finite_singleton _).insert _).insert _).insert _).isClosed

lemma mem_good {t : ℝ} : t ∈ good ↔ (0 < t ∧ t < π / 2) ∧ t ≠ φ ∧ t ≠ θ ∧ t ≠ π / 2 - θ ∧
    t ≠ π / 2 - φ := by
  simp only [good, Set.mem_sdiff, mem_Ioo, mem_insert_iff, mem_singleton_iff, not_or]

lemma good_reflect {t : ℝ} (ht : t ∈ good) : π / 2 - t ∈ good := by
  obtain ⟨⟨h0, h5⟩, h1, h2, h3, h4⟩ := mem_good.1 ht
  refine mem_good.2 ⟨⟨by linarith, by linarith⟩, fun h => h4 ?_, fun h => h3 ?_, fun h => h2 ?_,
    fun h => h1 ?_⟩ <;> linarith

lemma continuousAt_r_of_good {t : ℝ} (ht : t ∈ good) : ContinuousAt r t := by
  obtain ⟨⟨h0, h5⟩, h1, h2, h3, h4⟩ := mem_good.1 ht
  rcases lt_or_gt_of_ne h1 with a1 | a1
  · exact continuousAt_r (k := 0) (by norm_num) ⟨h0, a1⟩
  rcases lt_or_gt_of_ne h2 with a2 | a2
  · exact continuousAt_r (k := 1) (by norm_num) ⟨a1, a2⟩
  rcases lt_or_gt_of_ne h3 with a3 | a3
  · exact continuousAt_r (k := 2) (by norm_num) ⟨a2, a3⟩
  rcases lt_or_gt_of_ne h4 with a4 | a4
  · exact continuousAt_r (k := 3) (by norm_num) ⟨a3, a4⟩
  · exact continuousAt_r_top a4

lemma good_of_mem {a b : ℝ} {t : ℝ} (ht : t ∈ Ioo a b) (h0 : 0 ≤ a) (h5 : b ≤ π / 2)
    (h1 : φ ∉ Ioo a b) (h2 : θ ∉ Ioo a b) (h3 : π / 2 - θ ∉ Ioo a b) (h4 : π / 2 - φ ∉ Ioo a b) :
    t ∈ good :=
  mem_good.2 ⟨⟨h0.trans_lt ht.1, ht.2.trans_le h5⟩, fun h => h1 (h ▸ ht), fun h => h2 (h ▸ ht),
    fun h => h3 (h ▸ ht), fun h => h4 (h ▸ ht)⟩

/-! ## Derivatives of `x`, `y`, `p` -/

lemma hasDerivAt_x {t : ℝ} (ht : ContinuousAt r t) :
    HasDerivAt GerversSofa.x (r t * cos t) t := by
  have hf : HasDerivAt (fun u => ∫ s in (π / 2 - φ)..u, r s * cos s) (r t * cos t) t :=
    intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_r_mul continuous_cos _ _)
      (measurable_r.mul continuous_cos.measurable).stronglyMeasurable.stronglyMeasurableAtFilter
      (ht.mul continuous_cos.continuousAt)
  have e : GerversSofa.x = fun u => 1 + ∫ s in (π / 2 - φ)..u, r s * cos s := funext x_eq
  rw [e]
  exact hf.const_add 1

lemma hasDerivAt_y {t : ℝ} (ht : ContinuousAt r t) :
    HasDerivAt GerversSofa.y (-(r t * sin t)) t := by
  have hf : HasDerivAt (fun u => ∫ s in (π / 2 - φ)..u, r s * sin s) (r t * sin t) t :=
    intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_r_mul continuous_sin _ _)
      (measurable_r.mul continuous_sin.measurable).stronglyMeasurable.stronglyMeasurableAtFilter
      (ht.mul continuous_sin.continuousAt)
  have e : GerversSofa.y = fun u => -∫ s in (π / 2 - φ)..u, r s * sin s := funext y_eq
  rw [e]
  exact hf.neg

lemma hasDerivAt_xr {t : ℝ} (ht : ContinuousAt r (π / 2 - t)) :
    HasDerivAt (fun s => GerversSofa.x (π / 2 - s)) (-(r (π / 2 - t) * sin t)) t :=
  ((hasDerivAt_x ht).comp t ((hasDerivAt_id' t).const_sub (π / 2))).congr_deriv
    (by rw [cos_pi_div_two_sub]; ring)

lemma hasDerivAt_yr {t : ℝ} (ht : ContinuousAt r (π / 2 - t)) :
    HasDerivAt (fun s => GerversSofa.y (π / 2 - s)) (r (π / 2 - t) * cos t) t :=
  ((hasDerivAt_y ht).comp t ((hasDerivAt_id' t).const_sub (π / 2))).congr_deriv
    (by rw [sin_pi_div_two_sub]; ring)

/-- `p₁'`. -/
def dp₁ (t : ℝ) : ℝ := -GerversSofa.x (π / 2 - t) * sin t + GerversSofa.y (π / 2 - t) * cos t

/-- `p₂'`. -/
def dp₂ (t : ℝ) : ℝ :=
  -GerversSofa.y t * sin t - (4 * GerversSofa.x 0 - 2 - GerversSofa.x t) * cos t

lemma p₁_eq_fun : p₁ = fun γ => GerversSofa.x (π / 2 - γ) * cos γ
    + GerversSofa.y (π / 2 - γ) * sin γ - 1 := funext p₁_uniform

lemma p₂_eq_fun : p₂ = fun γ => GerversSofa.y γ * cos γ
    - (4 * GerversSofa.x 0 - 2 - GerversSofa.x γ) * sin γ - 1 := funext p₂_uniform

lemma hasDerivAt_p₁ {t : ℝ} (ht : ContinuousAt r (π / 2 - t)) : HasDerivAt p₁ (dp₁ t) t := by
  rw [p₁_eq_fun]
  refine ((((hasDerivAt_xr ht).fun_mul (hasDerivAt_cos t)).fun_add
    ((hasDerivAt_yr ht).fun_mul (hasDerivAt_sin t))).sub_const 1).congr_deriv ?_
  simp only [dp₁]; ring

lemma hasDerivAt_p₂ {t : ℝ} (ht : ContinuousAt r t) : HasDerivAt p₂ (dp₂ t) t := by
  rw [p₂_eq_fun]
  refine ((((hasDerivAt_y ht).fun_mul (hasDerivAt_cos t)).fun_sub
    (((hasDerivAt_x ht).const_sub (4 * GerversSofa.x 0 - 2)).fun_mul
      (hasDerivAt_sin t))).sub_const 1).congr_deriv ?_
  simp only [dp₂]; ring

lemma hasDerivAt_dp₁ {t : ℝ} (ht : ContinuousAt r (π / 2 - t)) :
    HasDerivAt dp₁ (r (π / 2 - t) - p₁ t - 1) t := by
  have e : dp₁ = fun s => -GerversSofa.x (π / 2 - s) * sin s + GerversSofa.y (π / 2 - s) * cos s :=
    rfl
  rw [e]
  refine (((hasDerivAt_xr ht).fun_neg.fun_mul (hasDerivAt_sin t)).fun_add
    ((hasDerivAt_yr ht).fun_mul (hasDerivAt_cos t))).congr_deriv ?_
  rw [p₁_uniform]
  linear_combination r (π / 2 - t) * sin_sq_add_cos_sq t

lemma hasDerivAt_dp₂ {t : ℝ} (ht : ContinuousAt r t) :
    HasDerivAt dp₂ (r t - p₂ t - 1) t := by
  have e : dp₂ = fun s => -GerversSofa.y s * sin s
      - (4 * GerversSofa.x 0 - 2 - GerversSofa.x s) * cos s := rfl
  rw [e]
  refine (((hasDerivAt_y ht).fun_neg.fun_mul (hasDerivAt_sin t)).fun_sub
    (((hasDerivAt_x ht).const_sub (4 * GerversSofa.x 0 - 2)).fun_mul
      (hasDerivAt_cos t))).congr_deriv ?_
  rw [p₂_uniform]
  linear_combination r t * sin_sq_add_cos_sq t

/-! ## Vertex curves and inner corner of `K = C(G)` -/

lemma edgeMax_Kg {t : ℝ} (h0 : 0 < t) (h1 : t < π / 2) (ht : ContinuousAt r (π / 2 - t)) :
    edgeMax Kg t = dp₁ t := by
  have hK := isCap_Kg
  have h2 : HasDerivWithinAt (supportFn Kg) (dp₁ t) (Ioi t) t := by
    refine ((hasDerivAt_p₁ ht).add_const 1).hasDerivWithinAt.congr_of_eventuallyEq ?_
      (supportFn_Kg ⟨h0.le, h1.le⟩)
    filter_upwards [Ioo_mem_nhdsGT h1] with s hs
    exact supportFn_Kg ⟨by linarith [hs.1], hs.2.le⟩
  exact (uniqueDiffWithinAt_Ioi t).eq_deriv _
    (hasDerivWithinAt_supportFn_Ioi hK.isCompact hK.nonempty t) h2

lemma edgeMax_Kg' {t : ℝ} (h0 : 0 < t) (h1 : t < π / 2) (ht : ContinuousAt r t) :
    edgeMax Kg (t + π / 2) = dp₂ t := by
  have hK := isCap_Kg
  have hp : HasDerivAt p₂ (dp₂ t) (t + π / 2 - π / 2) := by
    rw [add_sub_cancel_right]; exact hasDerivAt_p₂ ht
  have h2 : HasDerivWithinAt (supportFn Kg) (dp₂ t) (Ioi (t + π / 2)) (t + π / 2) := by
    refine ((hp.comp_sub_const (t + π / 2) (π / 2)).add_const 1).hasDerivWithinAt.congr_of_eventuallyEq
      ?_ (by rw [add_sub_cancel_right]; exact supportFn_Kg' ⟨h0.le, h1.le⟩)
    filter_upwards [Ioo_mem_nhdsGT (show t + π / 2 < π by linarith)] with s hs
    have := supportFn_Kg' (α := s - π / 2) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rwa [sub_add_cancel] at this
  exact (uniqueDiffWithinAt_Ioi _).eq_deriv _
    (hasDerivWithinAt_supportFn_Ioi hK.isCompact hK.nonempty _) h2

/-- **The vertex curve `v⁺_K` is Romik's `A`** (away from the break points). -/
theorem vtxP_Kg {t : ℝ} (hg : t ∈ good) : vtxP Kg t = ptA t := by
  obtain ⟨⟨h0, h1⟩, -⟩ := mem_good.1 hg
  have hsc := sin_sq_add_cos_sq t
  rw [vtxP, edgeMax_Kg h0 h1 (continuousAt_r_of_good (good_reflect hg)),
    supportFn_Kg ⟨h0.le, h1.le⟩, p₁_uniform, dp₁, ptA]
  refine ext_two ?_ ?_
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, u_coord_zero, v_coord_zero, pt_zero]
    linear_combination GerversSofa.x (π / 2 - t) * hsc
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, u_coord_one, v_coord_one, pt_one]
    linear_combination GerversSofa.y (π / 2 - t) * hsc

/-- **The vertex curve `v⁺_K(· + π/2)` is Romik's `C`** (away from the break points). -/
theorem vtxP_Kg_add {t : ℝ} (hg : t ∈ good) : vtxP Kg (t + π / 2) = ptC t := by
  obtain ⟨⟨h0, h1⟩, -⟩ := mem_good.1 hg
  have hsc := sin_sq_add_cos_sq t
  rw [vtxP, edgeMax_Kg' h0 h1 (continuousAt_r_of_good hg), supportFn_Kg' ⟨h0.le, h1.le⟩,
    u_add_pi_div_two, v_add_pi_div_two, p₂_uniform, dp₂, ptC]
  refine ext_two ?_ ?_
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul, u_coord_zero,
      v_coord_zero, pt_zero]
    linear_combination (4 * GerversSofa.x 0 - 2 - GerversSofa.x t) * hsc
  · simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul, u_coord_one,
      v_coord_one, pt_one]
    linear_combination GerversSofa.y t * hsc

lemma hasDerivAt_ptA {t : ℝ} (ht : ContinuousAt r (π / 2 - t)) :
    HasDerivAt ptA (r (π / 2 - t) • v t) t := by
  have e : ptA = fun s => GerversSofa.x (π / 2 - s) • e₀ + GerversSofa.y (π / 2 - s) • e₁ := rfl
  rw [e]
  refine (((hasDerivAt_xr ht).smul_const e₀).add ((hasDerivAt_yr ht).smul_const e₁)).congr_deriv ?_
  refine ext_two ?_ ?_ <;> simp [e₀, e₁]

lemma hasDerivAt_ptC {t : ℝ} (ht : ContinuousAt r t) :
    HasDerivAt ptC (-r t • u t) t := by
  have e : ptC = fun s => (4 * GerversSofa.x 0 - 2 - GerversSofa.x s) • e₀
      + GerversSofa.y s • e₁ := rfl
  rw [e]
  refine ((((hasDerivAt_x ht).const_sub (4 * GerversSofa.x 0 - 2)).smul_const e₀).add
    ((hasDerivAt_y ht).smul_const e₁)).congr_deriv ?_
  refine ext_two ?_ ?_ <;> simp [e₀, e₁]

/-- `A'(t) = r(π/2 − t) v_t`. -/
lemma hasDerivAt_vtxP {t : ℝ} (hg : t ∈ good) :
    HasDerivAt (vtxP Kg) (r (π / 2 - t) • v t) t := by
  refine (hasDerivAt_ptA (continuousAt_r_of_good (good_reflect hg))).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_good.mem_nhds hg] with s hs using vtxP_Kg hs

/-- `C'(t) = −r(t) u_t`. -/
lemma hasDerivAt_vtxP_add {t : ℝ} (hg : t ∈ good) :
    HasDerivAt (vtxP Kg) (-r t • u t) (t + π / 2) := by
  have hp : HasDerivAt ptC (-r t • u t) (t + π / 2 - π / 2) := by
    rw [add_sub_cancel_right]; exact hasDerivAt_ptC (continuousAt_r_of_good hg)
  refine (hp.comp_sub_const (t + π / 2) (π / 2)).congr_of_eventuallyEq ?_
  have hU : IsOpen ((fun s => s - π / 2) ⁻¹' good) :=
    isOpen_good.preimage (continuous_id.sub continuous_const)
  have hmem : t + π / 2 ∈ (fun s => s - π / 2) ⁻¹' good := by
    show t + π / 2 - π / 2 ∈ good; rwa [add_sub_cancel_right]
  filter_upwards [hU.mem_nhds hmem] with s hs
  have := vtxP_Kg_add (t := s - π / 2) hs
  rwa [sub_add_cancel] at this

lemma deriv_vtxP {t : ℝ} (hg : t ∈ good) : deriv (vtxP Kg) t = r (π / 2 - t) • v t :=
  (hasDerivAt_vtxP hg).deriv

lemma deriv_vtxP_add {t : ℝ} (hg : t ∈ good) : deriv (vtxP Kg) (t + π / 2) = -r t • u t :=
  (hasDerivAt_vtxP_add hg).deriv

/-- `x_K' = (p₁' − p₂) u + (p₁ + p₂') v`. -/
lemma hasDerivAt_innerCorner {t : ℝ} (hg : t ∈ good) :
    HasDerivAt (innerCorner Kg) ((dp₁ t - p₂ t) • u t + (p₁ t + dp₂ t) • v t) t := by
  have h := ((hasDerivAt_p₁ (continuousAt_r_of_good (good_reflect hg))).smul (hasDerivAt_u t)).add
    ((hasDerivAt_p₂ (continuousAt_r_of_good hg)).smul (hasDerivAt_v t))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq ?_
  · refine ext_two ?_ ?_ <;> simp <;> ring
  · filter_upwards [isOpen_good.mem_nhds hg] with s hs
    obtain ⟨⟨h0, h1⟩, -⟩ := mem_good.1 hs
    exact innerCorner_Kg ⟨h0.le, h1.le⟩

lemma deriv_innerCorner {t : ℝ} (hg : t ∈ good) :
    deriv (innerCorner Kg) t = (dp₁ t - p₂ t) • u t + (p₁ t + dp₂ t) • v t :=
  (hasDerivAt_innerCorner hg).deriv

/-! ## The tails -/

/-- The tail `B`: the envelope of the inner walls `ca = 0`. -/
def Bg (t : ℝ) : ℝ² := p₁ t • u t + dp₁ t • v t

/-- The tail `D`: the envelope of the inner walls `cb = 0`. -/
def Dg (t : ℝ) : ℝ² := -dp₂ t • u t + p₂ t • v t

lemma hasDerivAt_Bg {t : ℝ} (ht : ContinuousAt r (π / 2 - t)) :
    HasDerivAt Bg ((r (π / 2 - t) - 1) • v t) t := by
  have e : Bg = fun s => p₁ s • u s + dp₁ s • v s := rfl
  rw [e]
  refine (((hasDerivAt_p₁ ht).smul (hasDerivAt_u t)).add
    ((hasDerivAt_dp₁ ht).smul (hasDerivAt_v t))).congr_deriv ?_
  refine ext_two ?_ ?_ <;> simp <;> ring

lemma hasDerivAt_Dg {t : ℝ} (ht : ContinuousAt r t) :
    HasDerivAt Dg ((1 - r t) • u t) t := by
  have e : Dg = fun s => -dp₂ s • u s + p₂ s • v s := rfl
  rw [e]
  refine (((hasDerivAt_dp₂ ht).neg.smul (hasDerivAt_u t)).add
    ((hasDerivAt_p₂ ht).smul (hasDerivAt_v t))).congr_deriv ?_
  refine ext_two ?_ ?_ <;> simp <;> ring

lemma derivWithin_Bg {t : ℝ} (hg : t ∈ good) :
    derivWithin Bg (Ici t) t = (r (π / 2 - t) - 1) • v t :=
  (hasDerivAt_Bg (continuousAt_r_of_good (good_reflect hg))).hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_Ici t)

lemma derivWithin_Dg {t : ℝ} (hg : t ∈ good) :
    derivWithin Dg (Ici t) t = (1 - r t) • u t :=
  (hasDerivAt_Dg (continuousAt_r_of_good hg)).hasDerivWithinAt.derivWithin
    (uniqueDiffWithinAt_Ici t)

lemma continuous_dp₁ : Continuous dp₁ := by
  have hx := continuous_x
  have hy := continuous_y
  unfold dp₁; fun_prop

lemma continuous_dp₂ : Continuous dp₂ := by
  have hx := continuous_x
  have hy := continuous_y
  unfold dp₂; fun_prop

lemma continuous_Bg : Continuous Bg :=
  ((continuous_p₁.smul continuous_u).add (continuous_dp₁.smul continuous_v))

lemma continuous_Dg : Continuous Dg :=
  ((continuous_dp₂.neg.smul continuous_u).add (continuous_p₂.smul continuous_v))

/-- The tail `B` lies on the inner walls `⟪z, u_t⟫ = h_K(t) − 1`. -/
lemma Bg_wall {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) : ⟪Bg t, u t⟫ = supportFn Kg t - 1 := by
  rw [Bg, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u, inner_v_u,
    supportFn_Kg ht]
  ring

/-- The tail `D` lies on the inner walls `⟪z, v_t⟫ = h_K(t + π/2) − 1`. -/
lemma Dg_wall {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) :
    ⟪Dg t, u (t + π / 2)⟫ = supportFn Kg (t + π / 2) - 1 := by
  rw [u_add_pi_div_two, Dg, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_v,
    inner_v_v, supportFn_Kg' ht]
  ring

/-! ## Romik's identities -/

/-- `F = p₂ − p₁'`. -/
lemma p₂_sub_dp₁ (t : ℝ) : p₂ t - dp₁ t = (GerversSofa.y t - GerversSofa.y (π / 2 - t)) * cos t
    + (GerversSofa.x t + GerversSofa.x (π / 2 - t) + 2 - 4 * GerversSofa.x 0) * sin t - 1 := by
  rw [p₂_uniform, dp₁]; ring

/-- `p₁ + p₂' = F(π/2 − ·)`. -/
lemma p₁_add_dp₂ (t : ℝ) : p₁ t + dp₂ t = p₂ (π / 2 - t) - dp₁ (π / 2 - t) := by
  rw [p₁_uniform, dp₂, p₂_uniform, dp₁, sin_pi_div_two_sub, cos_pi_div_two_sub, sub_sub_cancel]
  ring

/-- **Romik's identity on `[θ, π/2 − θ]`**: `F = A + t − φ` (`= r`). -/
theorem F_piece2 {t : ℝ} (ht : t ∈ Icc θ (π / 2 - θ)) : p₂ t - dp₁ t = A + t - φ := by
  have h2 : t ∈ Icc (brk 2) (brk (2 + 1)) := ht
  have h2' : π / 2 - t ∈ Icc (brk 2) (brk (2 + 1)) :=
    ⟨by show θ ≤ π / 2 - t; linarith [ht.2], by show π / 2 - t ≤ π / 2 - θ; linarith [ht.1]⟩
  obtain ⟨-, -, -, -, -, -, e2, -, e4⟩ := gerver_spec
  rw [p₂_sub_dp₁, y_eq_yC (by norm_num) h2, y_eq_yC (by norm_num) h2', x_eq_xC (by norm_num) h2,
    x_eq_xC (by norm_num) h2', x_zero_eq, sin_pi_div_two_sub, cos_pi_div_two_sub]
  simp only [yC, xC, x0C, Fs, Fc, tailY, tailX, SY, SX, brk, ra, rb, rc, Nat.reduceAdd,
    sin_pi_div_two_sub, cos_pi_div_two_sub]
  linear_combination (-sin t) * e2 + (2 * cos θ * sin t) * e4
    + (A - φ + t + 1) * sin_sq_add_cos_sq t

/-- **Romik's identity on `[π/2 − θ, π/2 − φ]`**: `F = r`. -/
theorem F_piece3 {t : ℝ} (ht : t ∈ Icc (π / 2 - θ) (π / 2 - φ)) :
    p₂ t - dp₁ t = B - (π / 2 - t - φ) * (1 + A) / 2 - (π / 2 - t - φ) ^ 2 / 4 := by
  have h3 : t ∈ Icc (brk 3) (brk (3 + 1)) := ht
  have h1 : π / 2 - t ∈ Icc (brk 1) (brk (1 + 1)) :=
    ⟨by show φ ≤ π / 2 - t; linarith [ht.2], by show π / 2 - t ≤ θ; linarith [ht.1]⟩
  obtain ⟨-, -, -, -, -, -, e2, -, e4⟩ := gerver_spec
  rw [p₂_sub_dp₁, y_eq_yC (by norm_num) h3, y_eq_yC (by norm_num) h1, x_eq_xC (by norm_num) h3,
    x_eq_xC (by norm_num) h1, x_zero_eq, sin_pi_div_two_sub, cos_pi_div_two_sub]
  simp only [yC, xC, x0C, Fs, Fc, tailY, tailX, SY, SX, brk, ra, rb, rc, Nat.reduceAdd,
    sin_pi_div_two_sub, cos_pi_div_two_sub]
  linear_combination (-sin t) * e2 + (sin θ * cos t + 3 * cos θ * sin t) * e4
    + ((8 * A * φ - 4 * A * π + 8 * A * t + 16 * B - 4 * φ ^ 2 + 4 * φ * π - 8 * φ * t + 8 * φ
      - π ^ 2 + 4 * π * t - 4 * π - 4 * t ^ 2 + 8 * t + 16) / 16) * sin_sq_add_cos_sq t

/-- **Romik's identity on `[φ, θ]`**: `F = A + t − φ` (`= 2r − 1`). -/
theorem F_piece1 {t : ℝ} (ht : t ∈ Icc φ θ) : p₂ t - dp₁ t = A + t - φ := by
  have h1 : t ∈ Icc (brk 1) (brk (1 + 1)) := ht
  have h3 : π / 2 - t ∈ Icc (brk 3) (brk (3 + 1)) :=
    ⟨by show π / 2 - θ ≤ π / 2 - t; linarith [ht.2],
      by show π / 2 - t ≤ π / 2 - φ; linarith [ht.1]⟩
  obtain ⟨-, -, -, -, -, -, e2, -, e4⟩ := gerver_spec
  rw [p₂_sub_dp₁, y_eq_yC (by norm_num) h1, y_eq_yC (by norm_num) h3, x_eq_xC (by norm_num) h1,
    x_eq_xC (by norm_num) h3, x_zero_eq, sin_pi_div_two_sub, cos_pi_div_two_sub]
  simp only [yC, xC, x0C, Fs, Fc, tailY, tailX, SY, SX, brk, ra, rb, rc, Nat.reduceAdd,
    sin_pi_div_two_sub, cos_pi_div_two_sub]
  linear_combination (-sin t) * e2 + (-sin θ * cos t + 3 * cos θ * sin t) * e4
    + (A - φ + t + 1) * sin_sq_add_cos_sq t

/-- `F = r` on `(θ, π/2 − φ]`. -/
lemma F_eq_r {t : ℝ} (ht : t ∈ Ioc θ (π / 2 - φ)) : p₂ t - dp₁ t = r t := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  rcases le_total t (π / 2 - θ) with h | h
  · rw [F_piece2 ⟨ht.1.le, h⟩, r_def, if_neg (by linarith [ht.1]), if_neg (by linarith [ht.1]),
      if_pos h]
  · rw [F_piece3 ⟨h, ht.2⟩]
    rcases h.lt_or_eq with h' | h'
    · rw [r_def, if_neg (by linarith), if_neg (by linarith), if_neg (not_le.2 h'), if_pos ht.2]
    · -- at `t = π/2 − θ` both formulas agree (`E₄`)
      obtain ⟨-, -, -, -, -, -, -, -, e4⟩ := gerver_spec
      subst h'
      rw [r_def, if_neg (by linarith), if_neg (by linarith), if_pos le_rfl]
      linear_combination -e4

/-- `F = 2r − 1` on `(φ, θ]`. -/
lemma F_eq_two_r {t : ℝ} (ht : t ∈ Ioc φ θ) : p₂ t - dp₁ t = 2 * r t - 1 := by
  rw [F_piece1 ⟨ht.1.le, ht.2⟩, r_def, if_neg (not_le.2 ht.1), if_pos ht.2]
  ring

/-! ## Romik's ODEs -/

lemma inner_smul_u_u (a t : ℝ) : ⟪a • u t, u t⟫ = a := by
  rw [real_inner_smul_left, inner_u_u, mul_one]

lemma inner_smul_v_v (a t : ℝ) : ⟪a • v t, v t⟫ = a := by
  rw [real_inner_smul_left, inner_v_v, mul_one]

/-- **Thm 8.4.1 (1) + Thm 8.4.2 for Gerver's sofa**: Romik's ten ODEs for `K = C(G)` and the
tails `B`, `D`. -/
theorem gerverODE_Kg : GerverODE φ θ Kg Bg Dg := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  have nm : ∀ {c a b : ℝ}, (b ≤ c ∨ c ≤ a) → c ∉ Ioo a b := fun h hc => by
    rcases h with h | h <;> linarith [hc.1, hc.2]
  have g0 : ∀ t ∈ Ioo 0 φ, t ∈ good := fun t ht =>
    good_of_mem ht le_rfl (by linarith) (nm (Or.inl le_rfl)) (nm (Or.inl (by linarith)))
      (nm (Or.inl (by linarith))) (nm (Or.inl (by linarith)))
  have g1 : ∀ t ∈ Ioo φ θ, t ∈ good := fun t ht =>
    good_of_mem ht (by linarith) (by linarith) (nm (Or.inr le_rfl)) (nm (Or.inl le_rfl))
      (nm (Or.inl (by linarith))) (nm (Or.inl (by linarith)))
  have g2 : ∀ t ∈ Ioo θ (π / 2 - θ), t ∈ good := fun t ht =>
    good_of_mem ht (by linarith) (by linarith) (nm (Or.inr (by linarith))) (nm (Or.inr le_rfl))
      (nm (Or.inl le_rfl)) (nm (Or.inl (by linarith)))
  have g3 : ∀ t ∈ Ioo (π / 2 - θ) (π / 2 - φ), t ∈ good := fun t ht =>
    good_of_mem ht (by linarith) (by linarith) (nm (Or.inr (by linarith)))
      (nm (Or.inr (by linarith))) (nm (Or.inr le_rfl)) (nm (Or.inl le_rfl))
  have g4 : ∀ t ∈ Ioo (π / 2 - φ) (π / 2), t ∈ good := fun t ht =>
    good_of_mem ht (by linarith) le_rfl (nm (Or.inr (by linarith))) (nm (Or.inr (by linarith)))
      (nm (Or.inr (by linarith))) (nm (Or.inr le_rfl))
  refine
    { A_diff := fun t ht hb => (hasDerivAt_vtxP (show t ∈ good from ⟨ht, hb⟩)).differentiableAt
      C_diff := fun t ht hb => (hasDerivAt_vtxP_add (show t ∈ good from ⟨ht, hb⟩)).differentiableAt
      A_int := ?_
      C_int := ?_
      v1 := fun t ht => ?_
      u1 := fun t ht => ?_
      v2 := fun t ht => ?_
      u2 := fun t ht => ?_
      v3 := fun t ht => ?_
      u3 := fun t ht => ?_
      v4 := fun t ht => ?_
      u4 := fun t ht => ?_
      v5 := fun t ht => ?_
      u5 := fun t ht => ?_ }
  · -- `⟪A', v⟫ = r(π/2 − t)` off a finite set
    have hS : ({0, φ, θ, π / 2 - θ, π / 2 - φ, π / 2} : Set ℝ).Countable := by
      simp only [countable_insert, countable_singleton]
    have hr : IntervalIntegrable (fun t => r (π / 2 - t)) volume 0 (π / 2) := by
      have := (intervalIntegrable_r (π / 2 - 0) (π / 2 - π / 2)).comp_sub_left (π / 2)
      simpa using this
    refine (intervalIntegrable_congr_ae ?_).1 hr
    filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae (hS.ae_notMem volume)]
      with t ht1 ht2
    rw [uIoc_of_le (by positivity)] at ht1
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht2
    have hg : t ∈ good := mem_good.2 ⟨⟨ht1.1, lt_of_le_of_ne ht1.2 ht2.2.2.2.2.2⟩, ht2.2.1,
      ht2.2.2.1, ht2.2.2.2.1, ht2.2.2.2.2.1⟩
    rw [deriv_vtxP hg, inner_smul_v_v]
  · -- `⟪C', u⟫ = −r(t)` off a finite set
    have hS : ({0, φ, θ, π / 2 - θ, π / 2 - φ, π / 2} : Set ℝ).Countable := by
      simp only [countable_insert, countable_singleton]
    have hr : IntervalIntegrable (fun t => -r t) volume 0 (π / 2) := (intervalIntegrable_r _ _).neg
    refine (intervalIntegrable_congr_ae ?_).1 hr
    filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae (hS.ae_notMem volume)]
      with t ht1 ht2
    rw [uIoc_of_le (by positivity)] at ht1
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht2
    have hg : t ∈ good := mem_good.2 ⟨⟨ht1.1, lt_of_le_of_ne ht1.2 ht2.2.2.2.2.2⟩, ht2.2.1,
      ht2.2.2.1, ht2.2.2.2.1, ht2.2.2.2.2.1⟩
    rw [deriv_vtxP_add hg, inner_smul_u_u]
  · -- v1: `r(π/2 − t) = 0`
    rw [deriv_vtxP (g0 t ht), inner_smul_v_v, r_zero (by linarith [ht.2])]
  · -- u1: `r t = 1 − r t`
    rw [deriv_vtxP_add (g0 t ht), derivWithin_Dg (g0 t ht), ← neg_smul, neg_neg, inner_smul_u_u,
      inner_smul_u_u, r_of_le_φ ht.2.le]
    norm_num
  · -- v2: `r(π/2 − t) = p₁ + p₂'`
    rw [deriv_vtxP (g1 t ht), deriv_innerCorner (g1 t ht), inner_smul_v_v, inner_add_smul_v_v,
      p₁_add_dp₂, F_eq_r ⟨by linarith [ht.2], by linarith [ht.1]⟩]
  · -- u2: `r t = (1 − r t) − (p₁' − p₂)`
    rw [deriv_vtxP_add (g1 t ht), derivWithin_Dg (g1 t ht), deriv_innerCorner (g1 t ht),
      ← neg_smul, neg_neg, inner_smul_u_u, inner_sub_left, inner_smul_u_u, inner_add_smul_u_v]
    have := F_eq_two_r ⟨ht.1, ht.2.le⟩
    linarith
  · -- v3
    rw [deriv_vtxP (g2 t ht), deriv_innerCorner (g2 t ht), inner_smul_v_v, inner_add_smul_v_v,
      p₁_add_dp₂, F_eq_r ⟨by linarith [ht.2], by linarith [ht.1]⟩]
  · -- u3
    rw [deriv_vtxP_add (g2 t ht), deriv_innerCorner (g2 t ht), ← neg_smul, neg_neg,
      inner_smul_u_u, inner_neg_left, inner_add_smul_u_v]
    have := F_eq_r ⟨ht.1, by linarith [ht.2]⟩
    linarith
  · -- v4
    rw [deriv_vtxP (g3 t ht), deriv_innerCorner (g3 t ht), derivWithin_Bg (g3 t ht),
      inner_smul_v_v, inner_add_left, inner_neg_left, inner_smul_v_v, inner_add_smul_v_v, p₁_add_dp₂,
      F_eq_two_r ⟨by linarith [ht.2], by linarith [ht.1]⟩]
    ring
  · -- u4
    rw [deriv_vtxP_add (g3 t ht), deriv_innerCorner (g3 t ht), ← neg_smul, neg_neg,
      inner_smul_u_u, inner_neg_left, inner_add_smul_u_v]
    have := F_eq_r ⟨by linarith [ht.1], ht.2.le⟩
    linarith
  · -- v5: `r(π/2 − t) = 1 − r(π/2 − t)`
    rw [deriv_vtxP (g4 t ht), derivWithin_Bg (g4 t ht), inner_smul_v_v, inner_neg_left,
      inner_smul_v_v, r_of_le_φ (by linarith [ht.1])]
    norm_num
  · -- u5: `r t = 0`
    rw [deriv_vtxP_add (g4 t ht), ← neg_smul, neg_neg, inner_smul_u_u, r_zero ht.1]

end Sofa.GP
