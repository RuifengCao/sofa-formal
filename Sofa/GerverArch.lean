/-
# Sofa/GerverArch.lean — no inner quadrant of Gerver's hallways reaches the arch of the niche

The niche of `K = C(G)` is `N(K) = {y ≥ 0} ∩ ⋃_{s ∈ (0, π/2)} Q⁻(s)` with the open quadrants
`Q⁻(s) = {ca s < 0, cb s < 0}` (`ca s z = ⟪z, u_s⟫ − p₁(s)`, `cb s z = ⟪z, v_s⟫ − p₂(s)`).  Its
upper boundary is the *arch*

    D(t), t ∈ [0, θ]   (left tail),   x_K(t), t ∈ [φ, π/2 − φ]   (core),   B(t), t ∈ [π/2 − θ, π/2]

(`Dg`, `xKg`, `Bg`).  This file proves that **no point of the arch lies in any `Q⁻(s)`**
(`Dg_not_mem`, `xKg_not_mem`, `Bg_not_mem`), and that no inner quadrant reaches the `x`-axis
outside the arch (`cb_Dg_zero_nonneg`, `ca_Bg_half_nonneg`).

The two-parameter family of inequalities is reduced to one-parameter statements about the two
junction points `J_L = D(θ) = x_K(π/2 − φ)` and `J_R = B(π/2 − θ) = x_K(φ)`:

* along the tail `D` (`D' = (1 − r) u`) the functions `τ ↦ cb s (D τ)` and
  `τ ↦ ca s (D τ) + cb s (D τ)` are monotone (`1 − r > 0` on `[0, θ]`), and `cb s (D s) = 0`;
* along the core (`x_K' = −F u + G v`, with Romik's `F` increasing and `G` decreasing) the functions
  `τ ↦ ca s (x_K τ)`, `τ ↦ cb s (x_K τ)` are quasi-concave (`min_le_of_hasDerivAt_mul`);
* at the junction, `s ↦ cb s J_L` vanishes at `s = θ` (to second order) and at `s = π/2 − φ`, and
  satisfies `f'' + f = 1 − r`; it is nonnegative by the monotonicity along the envelope `D` where
  `r ≤ 1`, and by a Sturm-type argument (`f / cos(s − c)` is quasi-concave) where `r ≥ 1`;
* the reflection `(x, y) ↦ (4x₀ − 2 − x, y)` exchanges `ca s` and `cb (π/2 − s)`, `D` and `B`
  (`ca_refl`, `refl_Dg`), so the right tail follows from the left one.

STATUS: [PROOF-C] [AXIOM-CHECK] round 41 (2026-09-23, Opus 5.5), no `sorry`.
-/
import Sofa.GerverEnds
import Sofa.GerverInj

noncomputable section

open Real Set MeasureTheory intervalIntegral MovingSofa Filter Topology
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa

/-! ## Two calculus lemmas -/

/-- Monotonicity from a nonnegative derivative off a countable set (fundamental theorem of
calculus with countably many exceptions). -/
theorem monotoneOn_of_hasDerivAt_nonneg_off_countable {f f' : ℝ → ℝ} {a b : ℝ} {S : Set ℝ}
    (hS : S.Countable) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ∉ S → HasDerivAt f (f' x) x)
    (hi : IntervalIntegrable f' volume a b)
    (hnn : ∀ x ∈ Ioo a b, x ∉ S → 0 ≤ f' x) : MonotoneOn f (Icc a b) := by
  intro x hx y hy hxy
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have e := integral_eq_of_hasDerivAt_off_countable_of_le f f' hxy hS (hf.mono hsub)
    (fun z hz => hd z ⟨lt_of_le_of_lt hx.1 hz.1.1, lt_of_lt_of_le hz.1.2 hy.2⟩ hz.2)
    (hi.mono_set (by
      rw [uIcc_of_le hxy, uIcc_of_le (hx.1.trans (hxy.trans hy.2))]; exact hsub))
  have hpos : 0 ≤ ∫ z in x..y, f' z := by
    refine integral_nonneg_of_ae_restrict hxy ?_
    have hN : volume (S ∪ {x, y}) = 0 :=
      (hS.union ((countable_singleton y).insert x)).measure_zero volume
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with z hz hzI
    simp only [mem_union, mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact hnn z ⟨lt_of_le_of_lt hx.1 (lt_of_le_of_ne hzI.1 (Ne.symm hz.2.1)),
      lt_of_lt_of_le (lt_of_le_of_ne hzI.2 hz.2.2) hy.2⟩ hz.1
  linarith

/-- Antitonicity from a nonpositive derivative off a countable set. -/
theorem antitoneOn_of_hasDerivAt_nonpos_off_countable {f f' : ℝ → ℝ} {a b : ℝ} {S : Set ℝ}
    (hS : S.Countable) (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ∉ S → HasDerivAt f (f' x) x)
    (hi : IntervalIntegrable f' volume a b)
    (hnp : ∀ x ∈ Ioo a b, x ∉ S → f' x ≤ 0) : AntitoneOn f (Icc a b) := by
  have h := monotoneOn_of_hasDerivAt_nonneg_off_countable (f := fun x => -f x)
    (f' := fun x => -f' x) hS hf.neg (fun x hx hxS => (hd x hx hxS).neg) hi.neg
    (fun x hx hxS => neg_nonneg.2 (hnp x hx hxS))
  intro x hx y hy hxy
  have := h hx hy hxy
  simp only at this
  linarith

/-- **Quasi-concavity.**  If `f' = ω k` on `(a, b)` with `ω > 0`, and `k` stays `≤ 0` once it is
negative, then `f` lies above the smaller of its two end values. -/
theorem min_le_of_hasDerivAt_mul {f ω k : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (ω x * k x) x)
    (hω : ∀ x ∈ Ioo a b, 0 < ω x)
    (hk : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo a b, x ≤ y → k x < 0 → k y ≤ 0) :
    ∀ x ∈ Icc a b, min (f a) (f b) ≤ f x := by
  intro x hx
  by_cases hneg : ∃ z ∈ Ioc a x, z < b ∧ k z < 0
  · obtain ⟨z, hz, hzb, hkz⟩ := hneg
    have hanti : AntitoneOn f (Icc x b) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc x b) (hf.mono (Icc_subset_Icc hx.1 le_rfl))
      · intro w hw
        rw [interior_Icc] at hw
        exact (hd w ⟨lt_of_lt_of_le hz.1 (hz.2.trans hw.1.le), hw.2⟩).differentiableAt
          |>.differentiableWithinAt
      · intro w hw
        rw [interior_Icc] at hw
        have hw' : w ∈ Ioo a b := ⟨lt_of_lt_of_le hz.1 (hz.2.trans hw.1.le), hw.2⟩
        rw [(hd w hw').deriv]
        exact mul_nonpos_of_nonneg_of_nonpos (hω w hw').le
          (hk z ⟨hz.1, hzb⟩ w hw' (hz.2.trans hw.1.le) hkz)
    exact (min_le_right _ _).trans (hanti ⟨le_rfl, hx.2⟩ ⟨hx.2, le_rfl⟩ hx.2)
  · push Not at hneg
    have hmono : MonotoneOn f (Icc a x) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc a x) (hf.mono (Icc_subset_Icc le_rfl hx.2))
      · intro w hw
        rw [interior_Icc] at hw
        exact (hd w ⟨hw.1, lt_of_lt_of_le hw.2 hx.2⟩).differentiableAt.differentiableWithinAt
      · intro w hw
        rw [interior_Icc] at hw
        have hw' : w ∈ Ioo a b := ⟨hw.1, lt_of_lt_of_le hw.2 hx.2⟩
        rw [(hd w hw').deriv]
        exact mul_nonneg (hω w hw').le (hneg w ⟨hw.1, hw.2.le⟩ hw'.2)
    exact (min_le_left _ _).trans (hmono ⟨le_rfl, hx.1⟩ ⟨hx.1, le_rfl⟩ hx.1)

end Sofa

namespace Sofa.GP

open GC IA
open MovingSofa.GerversSofa (A B φ θ r)

/-! ## Romik's `F`, `G` and the inner corner -/

/-- Romik's `F = p₂ − p₁'`. -/
def Fr (t : ℝ) : ℝ := p₂ t - dp₁ t

/-- `G = p₁ + p₂'`, the mirror image of `F`. -/
def Gr (t : ℝ) : ℝ := p₁ t + dp₂ t

lemma Gr_eq (t : ℝ) : Gr t = Fr (π / 2 - t) := p₁_add_dp₂ t

/-- The inner corner `x_K(t) = p₁(t) u_t + p₂(t) v_t`, as a function on `ℝ`. -/
def xKg (t : ℝ) : ℝ² := p₁ t • u t + p₂ t • v t

lemma innerCorner_Kg_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (π / 2)) : innerCorner Kg t = xKg t :=
  innerCorner_Kg ht

lemma continuous_xKg : Continuous xKg :=
  (continuous_p₁.smul continuous_u).add (continuous_p₂.smul continuous_v)

lemma continuous_Fr : Continuous Fr := continuous_p₂.sub continuous_dp₁

lemma continuous_Gr : Continuous Gr := continuous_p₁.add continuous_dp₂

/-- `x_K' = −F u + G v` everywhere (`p₁`, `p₂` are `C¹`). -/
lemma hasDerivAt_xKg (t : ℝ) : HasDerivAt xKg ((-Fr t) • u t + Gr t • v t) t := by
  have e : xKg = fun s => p₁ s • u s + p₂ s • v s := rfl
  rw [e]
  refine (((hasDerivAt_p₁' t).smul (hasDerivAt_u t)).add
    ((hasDerivAt_p₂' t).smul (hasDerivAt_v t))).congr_deriv ?_
  refine ext_two ?_ ?_ <;> simp [Fr, Gr] <;> ring

lemma ca_xKg_self (t : ℝ) : ca t (xKg t) = 0 := by
  rw [ca, xKg, inner_add_smul_u_v]; ring

lemma cb_xKg_self (t : ℝ) : cb t (xKg t) = 0 := by
  rw [cb, xKg, inner_add_smul_v_v]; ring

lemma cb_Dg_self (t : ℝ) : cb t (Dg t) = 0 := by
  rw [cb, Dg, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_v, inner_v_v]
  ring

lemma ca_Dg_self (t : ℝ) : ca t (Dg t) = -Gr t := by
  rw [ca, Dg, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u, inner_v_u, Gr]
  ring

lemma ca_Bg_self (t : ℝ) : ca t (Bg t) = 0 := by
  rw [ca, Bg, inner_add_smul_u_v]; ring

lemma cb_Bg_self (t : ℝ) : cb t (Bg t) = -Fr t := by
  rw [cb, Bg, inner_add_smul_v_v, Fr]; ring

/-! ## `ca`, `cb` along curves -/

lemma hasDerivAt_ca_comp {γ : ℝ → ℝ²} {γ' : ℝ²} {τ : ℝ} (s : ℝ) (h : HasDerivAt γ γ' τ) :
    HasDerivAt (fun τ => ca s (γ τ)) ⟪γ', u s⟫ τ := by
  have := h.inner ℝ (hasDerivAt_const τ (u s))
  simp only [inner_zero_right, zero_add] at this
  exact this.sub_const (p₁ s)

lemma hasDerivAt_cb_comp {γ : ℝ → ℝ²} {γ' : ℝ²} {τ : ℝ} (s : ℝ) (h : HasDerivAt γ γ' τ) :
    HasDerivAt (fun τ => cb s (γ τ)) ⟪γ', v s⟫ τ := by
  have := h.inner ℝ (hasDerivAt_const τ (v s))
  simp only [inner_zero_right, zero_add] at this
  exact this.sub_const (p₂ s)

lemma hasDerivAt_ca_xKg (s τ : ℝ) :
    HasDerivAt (fun τ => ca s (xKg τ)) (-Fr τ * cos (s - τ) + Gr τ * sin (s - τ)) τ := by
  have h := hasDerivAt_ca_comp s (hasDerivAt_xKg τ)
  rwa [inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u_sub, inner_v_u_eq_sin] at h

lemma hasDerivAt_cb_xKg (s τ : ℝ) :
    HasDerivAt (fun τ => cb s (xKg τ)) (Fr τ * sin (s - τ) + Gr τ * cos (s - τ)) τ := by
  have h := hasDerivAt_cb_comp s (hasDerivAt_xKg τ)
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_v_eq_neg_sin, inner_v_v_eq_cos] at h
  convert h using 1; ring

lemma hasDerivAt_ca_Dg (s : ℝ) {τ : ℝ} (hr : ContinuousAt r τ) :
    HasDerivAt (fun τ => ca s (Dg τ)) ((1 - r τ) * cos (s - τ)) τ := by
  have h := hasDerivAt_ca_comp s (hasDerivAt_Dg hr)
  rwa [real_inner_smul_left, inner_u_u_sub] at h

lemma hasDerivAt_cb_Dg (s : ℝ) {τ : ℝ} (hr : ContinuousAt r τ) :
    HasDerivAt (fun τ => cb s (Dg τ)) (-((1 - r τ) * sin (s - τ))) τ := by
  have h := hasDerivAt_cb_comp s (hasDerivAt_Dg hr)
  rw [real_inner_smul_left, inner_u_v_eq_neg_sin] at h
  convert h using 1; ring

/-! ## The reflection `(x, y) ↦ (4x₀ − 2 − x, y)` -/

/-- The reflection of Gerver's sofa in its axis of symmetry. -/
def refl (z : ℝ²) : ℝ² := pt (4 * GerversSofa.x 0 - 2 - z 0) (z 1)

lemma p₂_reflect (s : ℝ) : p₂ (π / 2 - s) = p₁ s - (4 * GerversSofa.x 0 - 2) * cos s := by
  rw [p₂_uniform, p₁_uniform, cos_pi_div_two_sub, sin_pi_div_two_sub]; ring

lemma p₁_reflect (s : ℝ) : p₁ (π / 2 - s) = p₂ s + (4 * GerversSofa.x 0 - 2) * sin s := by
  have h := p₂_reflect (π / 2 - s)
  rw [sub_sub_cancel, cos_pi_div_two_sub] at h
  linarith

lemma dp₂_reflect (s : ℝ) : dp₂ (π / 2 - s) = -dp₁ s - (4 * GerversSofa.x 0 - 2) * sin s := by
  rw [dp₂, dp₁, cos_pi_div_two_sub, sin_pi_div_two_sub]; ring

lemma ca_refl (s : ℝ) (z : ℝ²) : ca s (refl z) = cb (π / 2 - s) z := by
  rw [ca_eq, cb_eq, refl, pt_zero, pt_one, sin_pi_div_two_sub, cos_pi_div_two_sub, p₂_reflect]
  ring

lemma cb_refl (s : ℝ) (z : ℝ²) : cb s (refl z) = ca (π / 2 - s) z := by
  rw [cb_eq, ca_eq, refl, pt_zero, pt_one, sin_pi_div_two_sub, cos_pi_div_two_sub, p₁_reflect]
  ring

lemma refl_coord_one (z : ℝ²) : refl z 1 = z 1 := by rw [refl, pt_one]

lemma refl_coord_zero (z : ℝ²) : refl z 0 = 4 * GerversSofa.x 0 - 2 - z 0 := by rw [refl, pt_zero]

lemma refl_Dg (t : ℝ) : refl (Dg (π / 2 - t)) = Bg t := by
  have e1 : Dg (π / 2 - t) 0 = dp₁ t * sin t - p₁ t * cos t + (4 * GerversSofa.x 0 - 2) := by
    simp only [Dg, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, u_coord_zero, v_coord_zero,
      dp₂_reflect, p₂_reflect, cos_pi_div_two_sub, sin_pi_div_two_sub]
    linear_combination (4 * GerversSofa.x 0 - 2) * sin_sq_add_cos_sq t
  have e2 : Dg (π / 2 - t) 1 = dp₁ t * cos t + p₁ t * sin t := by
    simp only [Dg, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, u_coord_one, v_coord_one,
      dp₂_reflect, p₂_reflect, cos_pi_div_two_sub, sin_pi_div_two_sub]
    ring
  refine ext_two ?_ ?_
  · rw [refl_coord_zero, e1]; simp [Bg]; ring
  · rw [refl_coord_one, e2]; simp [Bg]; ring

lemma refl_xKg (t : ℝ) : refl (xKg (π / 2 - t)) = xKg t := by
  refine ext_two ?_ ?_
  · rw [refl_coord_zero]
    simp only [xKg, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, u_coord_zero, v_coord_zero,
      p₁_reflect, p₂_reflect, cos_pi_div_two_sub, sin_pi_div_two_sub]
    linear_combination (-(4 * GerversSofa.x 0 - 2)) * sin_sq_add_cos_sq t
  · rw [refl_coord_one]
    simp only [xKg, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, u_coord_one, v_coord_one,
      p₁_reflect, p₂_reflect, cos_pi_div_two_sub, sin_pi_div_two_sub]
    ring

/-! ## Romik's `F` on the core -/

lemma Fr_lin {τ : ℝ} (h : τ ∈ Icc φ (π / 2 - θ)) : Fr τ = A + τ - φ := by
  rcases le_total τ θ with h' | h'
  · exact F_piece1 ⟨h.1, h'⟩
  · exact F_piece2 ⟨h', h.2⟩

lemma Fr_quad {τ : ℝ} (h : τ ∈ Icc (π / 2 - θ) (π / 2 - φ)) :
    Fr τ = B - (π / 2 - τ - φ) * (1 + A) / 2 - (π / 2 - τ - φ) ^ 2 / 4 := F_piece3 h

/-- On the quadratic piece `F` is at least its value `A + π/2 − θ − φ` at `π/2 − θ` (`E₄`). -/
lemma Fr_quad_ge {τ : ℝ} (h : τ ∈ Icc (π / 2 - θ) (π / 2 - φ)) :
    A + (π / 2 - θ) - φ ≤ Fr τ := by
  obtain ⟨p1, p2, t1, t2, a1, a2, b1, b2⟩ := bounds
  obtain ⟨-, -, -, -, -, -, -, -, e4⟩ := gerver_spec
  rw [Fr_quad h]
  have h1 : 0 ≤ (θ - φ - (π / 2 - τ - φ)) * (1 + A) :=
    mul_nonneg (by linarith [h.1]) (by linarith)
  have h2 : 0 ≤ (θ - φ - (π / 2 - τ - φ)) * (θ - φ + (π / 2 - τ - φ)) :=
    mul_nonneg (by linarith [h.1]) (by linarith [h.2])
  nlinarith [e4, h1, h2]

/-- **`F` is increasing on the core** `[φ, π/2 − φ]`. -/
lemma monotoneOn_Fr : MonotoneOn Fr (Icc φ (π / 2 - φ)) := by
  intro a ha b hb hab
  rcases le_total a (π / 2 - θ) with h1 | h1 <;> rcases le_total b (π / 2 - θ) with h2 | h2
  · rw [Fr_lin ⟨ha.1, h1⟩, Fr_lin ⟨hb.1, h2⟩]; linarith
  · rw [Fr_lin ⟨ha.1, h1⟩]; linarith [Fr_quad_ge ⟨h2, hb.2⟩]
  · have : a = b := le_antisymm hab (h2.trans h1)
    rw [this]
  · rw [Fr_quad ⟨h1, ha.2⟩, Fr_quad ⟨h2, hb.2⟩]
    obtain ⟨p1, p2, t1, t2, a1, a2, b1, b2⟩ := bounds
    have k : 0 ≤ (b - a) * ((π / 2 - a - φ) + (π / 2 - b - φ) + 2 * (1 + A)) :=
      mul_nonneg (by linarith) (by linarith [ha.2, hb.2])
    nlinarith [k]

lemma core_reflect {τ : ℝ} (h : τ ∈ Icc φ (π / 2 - φ)) : π / 2 - τ ∈ Icc φ (π / 2 - φ) :=
  ⟨by linarith [h.2], by linarith [h.1]⟩

lemma φ_le_half_sub : φ ≤ π / 2 - φ := by
  obtain ⟨p1, p2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  linarith

lemma Fr_ge_A {τ : ℝ} (h : τ ∈ Icc φ (π / 2 - φ)) : A ≤ Fr τ := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  have h0 : Fr φ = A := by rw [Fr_lin ⟨le_rfl, by linarith⟩]; ring
  rw [← h0]
  exact monotoneOn_Fr ⟨le_rfl, φ_le_half_sub⟩ h h.1

/-- **`G` is decreasing on the core.** -/
lemma antitoneOn_Gr : AntitoneOn Gr (Icc φ (π / 2 - φ)) := by
  intro a ha b hb hab
  rw [Gr_eq, Gr_eq]
  exact monotoneOn_Fr (core_reflect hb) (core_reflect ha) (by linarith)

lemma Gr_ge_A {τ : ℝ} (h : τ ∈ Icc φ (π / 2 - φ)) : A ≤ Gr τ := by
  rw [Gr_eq]; exact Fr_ge_A (core_reflect h)

lemma A_pos : 0 < A := by
  obtain ⟨-, -, -, -, a1, -⟩ := bounds
  linarith

/-! ## The point `s**` where `r = 1` -/

/-- The point `s** ∈ (π/2 − θ, π/2 − φ)` where `r = 1`: `r ≤ 1` before, `r ≥ 1` after. -/
def sR : ℝ := π / 2 - φ - (Real.sqrt ((1 + A) ^ 2 + 4 * (B - 1)) - (1 + A))

lemma sR_facts : π / 2 - θ < sR ∧ sR < π / 2 - φ := by
  obtain ⟨p1, p2, t1, t2, a1, a2, b1, b2⟩ := bounds
  obtain ⟨-, -, -, -, -, -, -, -, e4⟩ := gerver_spec
  have hpi := Real.pi_gt_d2
  have hpi' := Real.pi_lt_d2
  have hq0 : 0 ≤ (1 + A) ^ 2 + 4 * (B - 1) := by nlinarith
  have hqq := Real.sq_sqrt hq0
  have hqn := Real.sqrt_nonneg ((1 + A) ^ 2 + 4 * (B - 1))
  set q := Real.sqrt ((1 + A) ^ 2 + 4 * (B - 1)) with hq
  have e : sR = π / 2 - φ - (q - (1 + A)) := rfl
  constructor
  · have hm : 0 < θ - φ + (1 + A) := by linarith
    have : q < θ - φ + (1 + A) := by
      by_contra hc
      push Not at hc
      have := mul_le_mul hc hc hm.le hqn
      nlinarith [e4]
    rw [e]; linarith
  · have : 1 + A < q := by
      by_contra hc
      push Not at hc
      have := mul_le_mul hc hc hqn (by linarith)
      nlinarith
    rw [e]; linarith

lemma θ_lt_sR : θ < sR := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  linarith [sR_facts.1]

lemma r_le_one {τ : ℝ} (h : τ ≤ sR) : r τ ≤ 1 := by
  obtain ⟨p1, p2, t1, t2, a1, a2, b1, b2⟩ := bounds
  have hpi := Real.pi_gt_d2
  have hpi' := Real.pi_lt_d2
  have hq0 : 0 ≤ (1 + A) ^ 2 + 4 * (B - 1) := by nlinarith
  have hqq := Real.sq_sqrt hq0
  have hqn := Real.sqrt_nonneg ((1 + A) ^ 2 + 4 * (B - 1))
  set q := Real.sqrt ((1 + A) ^ 2 + 4 * (B - 1)) with hq
  have e : sR = π / 2 - φ - (q - (1 + A)) := rfl
  rw [r_def]
  split_ifs with c1 c2 c3 c4
  · norm_num
  · linarith
  · linarith
  · have hσ : q ≤ π / 2 - τ - φ + (1 + A) := by linarith
    have := mul_le_mul hσ hσ hqn (by linarith)
    nlinarith
  · norm_num

lemma one_le_r {τ : ℝ} (h1 : sR ≤ τ) (h2 : τ ≤ π / 2 - φ) : 1 ≤ r τ := by
  obtain ⟨p1, p2, t1, t2, a1, a2, b1, b2⟩ := bounds
  have hpi := Real.pi_gt_d2
  have hs := sR_facts
  have hq0 : 0 ≤ (1 + A) ^ 2 + 4 * (B - 1) := by nlinarith
  have hqq := Real.sq_sqrt hq0
  have hqn := Real.sqrt_nonneg ((1 + A) ^ 2 + 4 * (B - 1))
  set q := Real.sqrt ((1 + A) ^ 2 + 4 * (B - 1)) with hq
  have e : sR = π / 2 - φ - (q - (1 + A)) := rfl
  rw [r_def, if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_pos h2]
  have hσ : π / 2 - τ - φ + (1 + A) ≤ q := by linarith
  have := mul_le_mul hσ hσ (by linarith) hqn
  nlinarith

/-! ## Along the left tail -/

lemma continuous_ca_comp {γ : ℝ → ℝ²} (hγ : Continuous γ) (s : ℝ) :
    Continuous fun τ => ca s (γ τ) := by
  unfold ca; exact (hγ.inner continuous_const).sub continuous_const

lemma continuous_cb_comp {γ : ℝ → ℝ²} (hγ : Continuous γ) (s : ℝ) :
    Continuous fun τ => cb s (γ τ) := by
  unfold cb; exact (hγ.inner continuous_const).sub continuous_const

lemma intervalIntegrable_one_sub_r_mul {g : ℝ → ℝ} (hg : Continuous g) (a b : ℝ) :
    IntervalIntegrable (fun τ => (1 - r τ) * g τ) volume a b :=
  (intervalIntegrable_const.sub (intervalIntegrable_r a b)).mul_continuousOn hg.continuousOn

/-- Along the envelope `D`, `cb s (D τ)` is smallest at `τ = s` as long as `r ≤ 1`. -/
lemma cb_Dg_nonneg_low {s t : ℝ} (hs : s ∈ Icc 0 sR) (ht : t ∈ Icc 0 sR) :
    0 ≤ cb s (Dg t) := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  have hsR := sR_facts
  have hf := continuous_cb_comp continuous_Dg s
  have hd : ∀ τ ∈ Ioo (min s t) (max s t), τ ∉ brkSet →
      HasDerivAt (fun τ => cb s (Dg τ)) ((fun τ => -((1 - r τ) * sin (s - τ))) τ) τ :=
    fun τ _ hτ => hasDerivAt_cb_Dg s (continuousAt_r_of_not_mem hτ)
  have hi : IntervalIntegrable (fun τ => -((1 - r τ) * sin (s - τ))) volume (min s t) (max s t) :=
    (intervalIntegrable_one_sub_r_mul (g := fun τ => sin (s - τ)) (by fun_prop) _ _).neg
  rcases le_total t s with hts | hst
  · rw [min_eq_right hts, max_eq_left hts] at hd hi
    have hsign : ∀ τ ∈ Ioo t s, τ ∉ brkSet → -((1 - r τ) * sin (s - τ)) ≤ 0 := by
      intro τ hτ _
      have h1 : 0 ≤ 1 - r τ := by linarith [r_le_one (hτ.2.le.trans hs.2)]
      have h2 : 0 ≤ sin (s - τ) :=
        sin_nonneg_of_nonneg_of_le_pi (by linarith [hτ.2]) (by linarith [hτ.1, ht.1, hs.2])
      have := mul_nonneg h1 h2
      linarith
    have hanti := antitoneOn_of_hasDerivAt_nonpos_off_countable brkSet_countable
      hf.continuousOn hd hi hsign
    have := hanti ⟨le_rfl, hts⟩ ⟨hts, le_rfl⟩ hts
    simpa only [cb_Dg_self] using this
  · rw [min_eq_left hst, max_eq_right hst] at hd hi
    have hsign : ∀ τ ∈ Ioo s t, τ ∉ brkSet → 0 ≤ -((1 - r τ) * sin (s - τ)) := by
      intro τ hτ _
      have h1 : 0 ≤ 1 - r τ := by linarith [r_le_one (hτ.2.le.trans ht.2)]
      have h2 : sin (s - τ) ≤ 0 :=
        sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [hτ.1]) (by linarith [hτ.2, ht.2, hs.1])
      have := mul_nonpos_of_nonneg_of_nonpos h1 h2
      linarith
    have hmono := monotoneOn_of_hasDerivAt_nonneg_off_countable brkSet_countable
      hf.continuousOn hd hi hsign
    have := hmono ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
    simpa only [cb_Dg_self] using this

/-- For `s ≥ θ` the function `τ ↦ cb s (D τ)` decreases on `[0, θ]`. -/
lemma cb_Dg_ge_theta {s t : ℝ} (hs : s ∈ Icc θ (π / 2)) (ht : t ∈ Icc 0 θ) :
    cb s (Dg θ) ≤ cb s (Dg t) := by
  have hpi := Real.pi_gt_d2
  have hθ := θ_lt_sR
  have hf := continuous_cb_comp continuous_Dg s
  have hsign : ∀ τ ∈ Ioo t θ, τ ∉ brkSet → -((1 - r τ) * sin (s - τ)) ≤ 0 := by
    intro τ hτ _
    have h1 : 0 ≤ 1 - r τ := by linarith [r_le_one (hτ.2.le.trans hθ.le)]
    have h2 : 0 ≤ sin (s - τ) :=
      sin_nonneg_of_nonneg_of_le_pi (by linarith [hτ.2, hs.1]) (by linarith [hτ.1, ht.1, hs.2])
    have := mul_nonneg h1 h2
    linarith
  have hanti := antitoneOn_of_hasDerivAt_nonpos_off_countable
    (f := fun τ => cb s (Dg τ)) (f' := fun τ => -((1 - r τ) * sin (s - τ))) brkSet_countable
    hf.continuousOn (fun τ _ hτ => hasDerivAt_cb_Dg s (continuousAt_r_of_not_mem hτ))
    (intervalIntegrable_one_sub_r_mul (g := fun τ => sin (s - τ)) (by fun_prop) _ _).neg hsign
  exact hanti ⟨le_rfl, ht.2⟩ ⟨ht.2, le_rfl⟩ ht.2

/-- For `s ∈ [π/2 − φ, π/2]` the function `τ ↦ ca s (D τ) + cb s (D τ)` decreases on `[0, θ]`
(the tail moves in the directions `u_τ` with `s − τ ∈ [π/4, π/2]`). -/
lemma ca_add_cb_Dg_ge_theta {s t : ℝ} (hs : s ∈ Icc (π / 2 - φ) (π / 2)) (ht : t ∈ Icc 0 θ) :
    ca s (Dg θ) + cb s (Dg θ) ≤ ca s (Dg t) + cb s (Dg t) := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  have hpi' := Real.pi_lt_d2
  have hθ := θ_lt_sR
  have hf := (continuous_ca_comp continuous_Dg s).add (continuous_cb_comp continuous_Dg s)
  have hsign : ∀ τ ∈ Ioo t θ, τ ∉ brkSet →
      (1 - r τ) * cos (s - τ) + -((1 - r τ) * sin (s - τ)) ≤ 0 := by
    intro τ hτ _
    have h1 : 0 ≤ 1 - r τ := by linarith [r_le_one (hτ.2.le.trans hθ.le)]
    -- `cos x ≤ sin x` for `x = s − τ ∈ [π/4, π/2]`
    have h2 : cos (s - τ) ≤ sin (s - τ) := by
      rw [← sin_pi_div_two_sub]
      exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [hτ.1, ht.1, hs.2])
        (by linarith [hτ.1, ht.1, hs.2]) (by linarith [hτ.2, hs.1])
    have := mul_le_mul_of_nonneg_left h2 h1
    linarith
  have hanti := antitoneOn_of_hasDerivAt_nonpos_off_countable
    (f := fun τ => ca s (Dg τ) + cb s (Dg τ))
    (f' := fun τ => (1 - r τ) * cos (s - τ) + -((1 - r τ) * sin (s - τ))) brkSet_countable
    hf.continuousOn
    (fun τ _ hτ => (hasDerivAt_ca_Dg s (continuousAt_r_of_not_mem hτ)).add
      (hasDerivAt_cb_Dg s (continuousAt_r_of_not_mem hτ)))
    ((intervalIntegrable_one_sub_r_mul (g := fun τ => cos (s - τ)) (by fun_prop) _ _).add
      (intervalIntegrable_one_sub_r_mul (g := fun τ => sin (s - τ)) (by fun_prop) _ _).neg) hsign
  exact hanti ⟨le_rfl, ht.2⟩ ⟨ht.2, le_rfl⟩ ht.2

/-! ## The junction points -/

lemma Dg_theta : Dg θ = xKg (π / 2 - φ) := by
  obtain ⟨p1, p2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  rw [Dg_end, innerCorner_Kg ⟨by linarith, by linarith⟩]; rfl

lemma Bg_start' : Bg (π / 2 - θ) = xKg φ := by
  obtain ⟨p1, p2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  rw [Bg_start, innerCorner_Kg ⟨by linarith, by linarith⟩]; rfl

lemma xKg_phi_refl : xKg φ = refl (Dg θ) := by rw [Dg_theta, refl_xKg]

lemma ca_xKg (s τ : ℝ) : ca s (xKg τ) = p₁ τ * cos (s - τ) + p₂ τ * sin (s - τ) - p₁ s := by
  rw [ca, xKg, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u_sub, inner_v_u_eq_sin]

lemma cb_xKg (s τ : ℝ) : cb s (xKg τ) = -(p₁ τ * sin (s - τ)) + p₂ τ * cos (s - τ) - p₂ s := by
  rw [cb, xKg, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_v_eq_neg_sin, inner_v_v_eq_cos]
  ring

lemma continuous_ca_const (J : ℝ²) : Continuous fun s => ca s J := by
  unfold ca; exact (continuous_const.inner continuous_u).sub continuous_p₁

lemma continuous_cb_const (J : ℝ²) : Continuous fun s => cb s J := by
  unfold cb; exact (continuous_const.inner continuous_v).sub continuous_p₂

lemma hasDerivAt_ca_pt (J : ℝ²) (s : ℝ) : HasDerivAt (fun s => ca s J) (⟪J, v s⟫ - dp₁ s) s := by
  have h1 := (hasDerivAt_const s J).inner ℝ (hasDerivAt_u s)
  simp only [inner_zero_left, add_zero] at h1
  exact h1.sub (hasDerivAt_p₁' s)

lemma hasDerivAt_cb_pt (J : ℝ²) (s : ℝ) :
    HasDerivAt (fun s => cb s J) (-⟪J, u s⟫ - dp₂ s) s := by
  have h1 := (hasDerivAt_const s J).inner ℝ (hasDerivAt_v s)
  simp only [inner_neg_right, inner_zero_left, add_zero] at h1
  exact h1.sub (hasDerivAt_p₂' s)

/-- `p₁`, `p₂` and their derivatives near `π/2`: there `r(π/2 − ·) = 1/2` and `r = 0`. -/
lemma p₁_top {s : ℝ} (hs : s ∈ Icc (π / 2 - φ) (π / 2)) :
    p₁ s = GerversSofa.x 0 * cos s + sin s / 2 - 1 / 2 := by
  have hm : π / 2 - s ∈ Icc (0 : ℝ) φ := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  rw [p₁_uniform, x_piece0 hm, y_piece0 hm, sin_pi_div_two_sub, cos_pi_div_two_sub]
  linear_combination (1 / 2 : ℝ) * sin_sq_add_cos_sq s

lemma dp₁_top {s : ℝ} (hs : s ∈ Icc (π / 2 - φ) (π / 2)) :
    dp₁ s = -GerversSofa.x 0 * sin s + cos s / 2 := by
  have hm : π / 2 - s ∈ Icc (0 : ℝ) φ := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  rw [dp₁, x_piece0 hm, y_piece0 hm, sin_pi_div_two_sub, cos_pi_div_two_sub]
  ring

lemma p₂_top {s : ℝ} (hs : π / 2 - φ ≤ s) : p₂ s = (3 - 4 * GerversSofa.x 0) * sin s - 1 := by
  rw [p₂_uniform, x_of_ge hs, y_of_ge hs]; ring

lemma dp₂_top {s : ℝ} (hs : π / 2 - φ ≤ s) : dp₂ s = (3 - 4 * GerversSofa.x 0) * cos s := by
  rw [dp₂, x_of_ge hs, y_of_ge hs]; ring

lemma p₁_JL : p₁ (π / 2 - φ) = GerversSofa.x 0 * sin φ + cos φ / 2 - 1 / 2 := by
  obtain ⟨p1, p2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  rw [p₁_top ⟨le_rfl, by linarith⟩, cos_pi_div_two_sub, sin_pi_div_two_sub]

lemma p₂_JL : p₂ (π / 2 - φ) = (3 - 4 * GerversSofa.x 0) * cos φ - 1 := by
  rw [p₂_top le_rfl, sin_pi_div_two_sub]

/-- Crude bounds on `p₁(π/2 − φ)`, `p₂(π/2 − φ)` (the coordinates of `J_L` in the frame
`u_{π/2−φ}`, `v_{π/2−φ}`) and on `sin φ`, `cos φ`. -/
lemma JL_bounds : p₁ (π / 2 - φ) ≤ 1 / 100 ∧ 119 / 100 ≤ p₂ (π / 2 - φ) ∧
    sin φ ≤ 1 / 25 ∧ 0 ≤ sin φ ∧ 9992 / 10000 ≤ cos φ ∧ cos φ ≤ 1 := by
  obtain ⟨p1, p2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  obtain ⟨x01, x02⟩ := x0_bounds
  have hs1 : sin φ ≤ φ := sin_le (by linarith)
  have hs0 : 0 ≤ sin φ := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hc0 : 1 - φ ^ 2 / 2 ≤ cos φ := one_sub_sq_div_two_le_cos
  have hc1 : cos φ ≤ 1 := cos_le_one φ
  have hφ2 : φ ^ 2 ≤ 16 / 10000 := by nlinarith
  refine ⟨?_, ?_, by linarith, hs0, by linarith, hc1⟩
  · rw [p₁_JL]; nlinarith
  · rw [p₂_JL]; nlinarith

/-- **(J4)** `ca s J_L ≥ 0` for `s ∈ [π/2 − φ, π/2]`. -/
lemma ca_JL_nonneg_top {s : ℝ} (hs : s ∈ Icc (π / 2 - φ) (π / 2)) : 0 ≤ ca s (Dg θ) := by
  obtain ⟨p1, p2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  obtain ⟨x01, x02⟩ := x0_bounds
  obtain ⟨ha, hb, hs1, hs0, hc0, hc1⟩ := JL_bounds
  rw [Dg_theta]
  have hmono : MonotoneOn (fun s => ca s (xKg (π / 2 - φ))) (Icc (π / 2 - φ) (π / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (continuous_ca_const _).continuousOn
      (fun s _ => (hasDerivAt_ca_pt _ s).differentiableAt.differentiableWithinAt)
    intro s hs
    rw [interior_Icc] at hs
    rw [(hasDerivAt_ca_pt _ s).deriv, dp₁_top ⟨hs.1.le, hs.2.le⟩, xKg, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, inner_u_v_eq_neg_sin, inner_v_v_eq_cos]
    set δ := s - (π / 2 - φ) with hδ
    have hδ0 : 0 ≤ δ := by linarith [hs.1]
    have hδ1 : δ ≤ φ := by linarith [hs.2]
    have hsd : sin δ ≤ 1 / 25 := (sin_le hδ0).trans (by linarith)
    have hsd0 : 0 ≤ sin δ := sin_nonneg_of_nonneg_of_le_pi hδ0 (by linarith)
    have hcd : 9992 / 10000 ≤ cos δ := by
      have := one_sub_sq_div_two_le_cos (x := δ)
      nlinarith
    have hss : 0 ≤ sin s := sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.1]) (by linarith [hs.2])
    have hcs : cos s ≤ 1 := cos_le_one s
    have k1 := mul_le_mul_of_nonneg_right ha hsd0
    have k2 := mul_le_mul hb hcd (by norm_num) (by linarith)
    have k3 := mul_nonneg (by linarith : (0 : ℝ) ≤ GerversSofa.x 0) hss
    nlinarith
  have := hmono ⟨le_rfl, by linarith⟩ hs hs.1
  simpa only [ca_xKg_self] using this

/-- **(J5)** `ca s J_L + cb s J_L ≥ 0` for `s ∈ [π/2 − φ, π/2]`. -/
lemma ca_add_cb_JL_top {s : ℝ} (hs : s ∈ Icc (π / 2 - φ) (π / 2)) :
    0 ≤ ca s (Dg θ) + cb s (Dg θ) := by
  obtain ⟨p1, p2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  obtain ⟨x01, x02⟩ := x0_bounds
  obtain ⟨ha, hb, hs1, hs0, hc0, hc1⟩ := JL_bounds
  rw [Dg_theta]
  have hmono : MonotoneOn (fun s => ca s (xKg (π / 2 - φ)) + cb s (xKg (π / 2 - φ)))
      (Icc (π / 2 - φ) (π / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      ((continuous_ca_const _).add (continuous_cb_const _)).continuousOn
      (fun s _ => ((hasDerivAt_ca_pt _ s).add (hasDerivAt_cb_pt _ s)).differentiableAt
        |>.differentiableWithinAt)
    intro s hs
    rw [interior_Icc] at hs
    rw [((hasDerivAt_ca_pt _ s).add (hasDerivAt_cb_pt _ s)).deriv, dp₁_top ⟨hs.1.le, hs.2.le⟩,
      dp₂_top hs.1.le, xKg, inner_add_left, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, inner_u_v_eq_neg_sin, inner_v_v_eq_cos,
      inner_u_u_sub, inner_v_u_eq_sin]
    set δ := s - (π / 2 - φ) with hδ
    have hδ0 : 0 ≤ δ := by linarith [hs.1]
    have hδ1 : δ ≤ φ := by linarith [hs.2]
    have hsd : sin δ ≤ 1 / 25 := (sin_le hδ0).trans (by linarith)
    have hsd0 : 0 ≤ sin δ := sin_nonneg_of_nonneg_of_le_pi hδ0 (by linarith)
    have hcd : 9992 / 10000 ≤ cos δ := by
      have := one_sub_sq_div_two_le_cos (x := δ)
      nlinarith
    have hcd1 : cos δ ≤ 1 := cos_le_one δ
    have hss : 0 ≤ sin s := sin_nonneg_of_nonneg_of_le_pi (by linarith [hs.1]) (by linarith [hs.2])
    -- `cos s = sin (π/2 − s) ≤ π/2 − s ≤ φ`
    have hcs : cos s ≤ 1 / 25 := by
      rw [← sin_pi_div_two_sub]; exact (sin_le (by linarith [hs.2])).trans (by linarith [hs.1])
    have hcs0 : 0 ≤ cos s := cos_nonneg_of_mem_Icc ⟨by linarith [hs.1], hs.2.le⟩
    have k1 := mul_le_mul_of_nonneg_right ha (add_nonneg hsd0 (by linarith : (0 : ℝ) ≤ cos δ))
    have k2 := mul_le_mul_of_nonneg_right hb (by linarith : (0 : ℝ) ≤ cos δ - sin δ)
    have k3 := mul_nonneg (by linarith : (0 : ℝ) ≤ GerversSofa.x 0) hss
    have k4 := mul_le_mul_of_nonneg_right (by linarith : (7 / 2 : ℝ) - 4 * GerversSofa.x 0 ≤ 7 / 2) hcs0
    nlinarith
  have := hmono ⟨le_rfl, by linarith⟩ hs hs.1
  simpa only [ca_xKg_self, cb_xKg_self, add_zero] using this

/-- **The Sturm argument.**  On `[s**, π/2 − φ]`, where `r ≥ 1`, the function `f(s) = cb s J_L`
satisfies `f'' + f = 1 − r ≤ 0`, `f(s**) ≥ 0` and `f(π/2 − φ) = 0`; so `f / cos(· − c)` is
quasi-concave (`c` the midpoint) and `f ≥ 0`. -/
lemma cb_JL_sturm {s₀ : ℝ} (hs₀ : s₀ ∈ Icc sR (π / 2 - φ)) : 0 ≤ cb s₀ (Dg θ) := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  have hsR := sR_facts
  obtain ⟨c, hc⟩ : ∃ c, c = (sR + (π / 2 - φ)) / 2 := ⟨_, rfl⟩
  have hcos : ∀ s ∈ Icc sR (π / 2 - φ), 0 < cos (s - c) := by
    intro s hs
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [hs.1, hs.2]
  -- `W = f' cos(· − c) + f sin(· − c)`, `W' = (f'' + f) cos(· − c) = (1 − r) cos(· − c)`
  let W : ℝ → ℝ := fun s => (-⟪Dg θ, u s⟫ - dp₂ s) * cos (s - c) + cb s (Dg θ) * sin (s - c)
  have hcd : ∀ s, HasDerivAt (fun s => cos (s - c)) (-sin (s - c)) s := fun s =>
    (((hasDerivAt_id' s).sub_const c).cos).congr_deriv (by ring)
  have hsd : ∀ s, HasDerivAt (fun s => sin (s - c)) (cos (s - c)) s := fun s =>
    (((hasDerivAt_id' s).sub_const c).sin).congr_deriv (by ring)
  have hWd : ∀ s ∈ Ioo sR (π / 2 - φ), HasDerivAt W ((1 - r s) * cos (s - c)) s := by
    intro s hs
    have hr : ContinuousAt r s := by
      apply continuousAt_r_of_not_mem
      simp only [brkSet, mem_insert_iff, mem_singleton_iff, not_or]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> linarith [hs.1, hs.2]
    have h1 := (hasDerivAt_const s (Dg θ)).inner ℝ (hasDerivAt_u s)
    simp only [inner_zero_left, add_zero] at h1
    have hf' : HasDerivAt (fun s => -⟪Dg θ, u s⟫ - dp₂ s)
        (-⟪Dg θ, v s⟫ - (r s - p₂ s - 1)) s := h1.neg.sub (hasDerivAt_dp₂ hr)
    refine ((hf'.mul (hcd s)).add ((hasDerivAt_cb_pt (Dg θ) s).mul (hsd s))).congr_deriv ?_
    simp only [cb]
    ring
  have hWc : Continuous W :=
    ((((continuous_const.inner continuous_u).neg.sub continuous_dp₂).mul
      (continuous_cos.comp (continuous_id.sub continuous_const))).add
      ((continuous_cb_const _).mul (continuous_sin.comp (continuous_id.sub continuous_const))))
  have hWanti : AntitoneOn W (Icc sR (π / 2 - φ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hWc.continuousOn
    · intro s hs
      rw [interior_Icc] at hs
      exact (hWd s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hWd s hs).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [one_le_r hs.1.le hs.2.le])
        (hcos s ⟨hs.1.le, hs.2.le⟩).le
  -- `g = f / cos(· − c)` has `g' = W / cos²(· − c)`
  have hgd : ∀ s ∈ Ioo sR (π / 2 - φ),
      HasDerivAt (fun s => cb s (Dg θ) / cos (s - c)) (1 / cos (s - c) ^ 2 * W s) s := by
    intro s hs
    have hc0 := (hcos s ⟨hs.1.le, hs.2.le⟩).ne'
    refine ((hasDerivAt_cb_pt (Dg θ) s).div (hcd s) hc0).congr_deriv ?_
    simp only [W]
    field_simp
    ring
  have hω : ∀ s ∈ Ioo sR (π / 2 - φ), 0 < 1 / cos (s - c) ^ 2 := fun s hs => by
    have := hcos s ⟨hs.1.le, hs.2.le⟩
    positivity
  have hk : ∀ x ∈ Ioo sR (π / 2 - φ), ∀ y ∈ Ioo sR (π / 2 - φ), x ≤ y → W x < 0 → W y ≤ 0 :=
    fun x hx y hy hxy hWx => (hWanti ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ hxy).trans hWx.le
  have hgc : ContinuousOn (fun s => cb s (Dg θ) / cos (s - c)) (Icc sR (π / 2 - φ)) :=
    (continuous_cb_const _).continuousOn.div
      (continuous_cos.comp (continuous_id.sub continuous_const)).continuousOn
      (fun s hs => (hcos s hs).ne')
  have hmin := min_le_of_hasDerivAt_mul hgc hgd hω hk s₀ hs₀
  have ha : 0 ≤ cb sR (Dg θ) / cos (sR - c) :=
    div_nonneg (cb_Dg_nonneg_low ⟨by linarith, le_rfl⟩ ⟨by linarith, θ_lt_sR.le⟩)
      (hcos sR ⟨le_rfl, hsR.2.le⟩).le
  have hb : cb (π / 2 - φ) (Dg θ) / cos (π / 2 - φ - c) = 0 := by
    rw [Dg_theta, cb_xKg_self, zero_div]
  have hg0 : 0 ≤ cb s₀ (Dg θ) / cos (s₀ - c) := le_trans (le_min ha hb.ge) hmin
  have := mul_nonneg hg0 (hcos s₀ hs₀).le
  rwa [div_mul_cancel₀ _ (hcos s₀ hs₀).ne'] at this

/-- **(J1)** `cb s J_L ≥ 0` for `s ∈ [0, π/2 − φ]`. -/
theorem cb_JL_nonneg {s : ℝ} (hs : s ∈ Icc 0 (π / 2 - φ)) : 0 ≤ cb s (Dg θ) := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  rcases le_total s sR with h | h
  · exact cb_Dg_nonneg_low ⟨hs.1, h⟩ ⟨by linarith, θ_lt_sR.le⟩
  · exact cb_JL_sturm ⟨h, hs.2⟩

/-- **(J2)** `ca s J_R ≥ 0` for `s ∈ [φ, π/2]` (mirror image of (J1)). -/
theorem ca_JR_nonneg {s : ℝ} (hs : s ∈ Icc φ (π / 2)) : 0 ≤ ca s (xKg φ) := by
  rw [xKg_phi_refl, ca_refl]; exact cb_JL_nonneg ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-- **(J3)** `cb s J_R ≥ 0` for `s ∈ [0, φ]` (mirror image of (J4)). -/
theorem cb_JR_nonneg {s : ℝ} (hs : s ∈ Icc 0 φ) : 0 ≤ cb s (xKg φ) := by
  rw [xKg_phi_refl, cb_refl]; exact ca_JL_nonneg_top ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-! ## No inner quadrant reaches the arch -/

/-- The left tail lies above the inner walls `cb s = 0` for `s ≤ π/2 − φ`. -/
lemma cb_Dg_nonneg {t s : ℝ} (ht : t ∈ Icc 0 θ) (hs : s ∈ Icc 0 (π / 2 - φ)) :
    0 ≤ cb s (Dg t) := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  rcases le_total s θ with h | h
  · exact cb_Dg_nonneg_low ⟨hs.1, h.trans θ_lt_sR.le⟩ ⟨ht.1, ht.2.trans θ_lt_sR.le⟩
  · exact (cb_JL_nonneg hs).trans (cb_Dg_ge_theta ⟨h, by linarith [hs.2]⟩ ht)

/-- **No inner quadrant contains a point of the left tail.** -/
theorem Dg_not_mem {t s : ℝ} (ht : t ∈ Icc 0 θ) (hs : s ∈ Ioo 0 (π / 2)) :
    ¬(ca s (Dg t) < 0 ∧ cb s (Dg t) < 0) := by
  rintro ⟨h1, h2⟩
  rcases le_total s (π / 2 - φ) with h | h
  · exact absurd h2 (not_lt.2 (cb_Dg_nonneg ht ⟨hs.1.le, h⟩))
  · have k1 := ca_add_cb_Dg_ge_theta ⟨h, hs.2.le⟩ ht
    have k2 := ca_add_cb_JL_top ⟨h, hs.2.le⟩
    linarith

/-- On the core, `ca s (x_K t) ≥ 0` for `t ≤ s` (`τ ↦ ca s (x_K τ)` is quasi-concave). -/
lemma ca_xKg_nonneg {t s : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) (hs : s ∈ Ioo 0 (π / 2))
    (hts : t ≤ s) : 0 ≤ ca s (xKg t) := by
  obtain ⟨p1, p2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  obtain ⟨m, hm⟩ : ∃ m, m = min s (π / 2 - φ) := ⟨_, rfl⟩
  have hm1 : m ≤ s := hm ▸ min_le_left _ _
  have hm2 : m ≤ π / 2 - φ := hm ▸ min_le_right _ _
  have htm : t ≤ m := hm ▸ le_min hts ht.2
  have hω : ∀ τ ∈ Ioo φ m, 0 < cos (s - τ) := fun τ hτ =>
    cos_pos_of_mem_Ioo ⟨by linarith [hτ.2], by linarith [hs.2, hτ.1]⟩
  have hd : ∀ τ ∈ Ioo φ m, HasDerivAt (fun τ => ca s (xKg τ))
      (cos (s - τ) * (Gr τ * tan (s - τ) - Fr τ)) τ := by
    intro τ hτ
    have hc := (hω τ hτ).ne'
    refine (hasDerivAt_ca_xKg s τ).congr_deriv ?_
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    ring
  have hk : ∀ x ∈ Ioo φ m, ∀ y ∈ Ioo φ m, x ≤ y →
      Gr x * tan (s - x) - Fr x < 0 → Gr y * tan (s - y) - Fr y ≤ 0 := by
    intro x hx y hy hxy hkx
    have hxc : x ∈ Icc φ (π / 2 - φ) := ⟨hx.1.le, hx.2.le.trans hm2⟩
    have hyc : y ∈ Icc φ (π / 2 - φ) := ⟨hy.1.le, hy.2.le.trans hm2⟩
    have h1 : Gr y ≤ Gr x := antitoneOn_Gr hxc hyc hxy
    have h2 : Fr x ≤ Fr y := monotoneOn_Fr hxc hyc hxy
    have h3 : tan (s - y) ≤ tan (s - x) :=
      strictMonoOn_tan.monotoneOn ⟨by linarith [hy.2], by linarith [hs.2, hy.1]⟩
        ⟨by linarith [hx.2], by linarith [hs.2, hx.1]⟩ (by linarith)
    have h4 : 0 ≤ tan (s - y) :=
      tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith [hy.2]) (by linarith [hs.2, hy.1])
    have := mul_le_mul h1 h3 h4 ((Gr_ge_A hxc).trans' A_pos.le)
    linarith
  have hmin := min_le_of_hasDerivAt_mul ((continuous_ca_comp continuous_xKg s).continuousOn)
    hd hω hk t ⟨ht.1, htm⟩
  have hφ : 0 ≤ ca s (xKg φ) := ca_JR_nonneg ⟨ht.1.trans hts, hs.2.le⟩
  have hmv : 0 ≤ ca s (xKg m) := by
    rcases le_total s (π / 2 - φ) with h | h
    · rw [hm, min_eq_left h, ca_xKg_self]
    · rw [hm, min_eq_right h, ← Dg_theta]; exact ca_JL_nonneg_top ⟨h, hs.2.le⟩
  exact le_trans (le_min hφ hmv) hmin

/-- On the core, `cb s (x_K t) ≥ 0` for `s ≤ t`. -/
lemma cb_xKg_nonneg {t s : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) (hs : s ∈ Ioo 0 (π / 2))
    (hst : s ≤ t) : 0 ≤ cb s (xKg t) := by
  obtain ⟨p1, p2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  obtain ⟨m, hm⟩ : ∃ m, m = max s φ := ⟨_, rfl⟩
  have hm1 : s ≤ m := hm ▸ le_max_left _ _
  have hm2 : φ ≤ m := hm ▸ le_max_right _ _
  have hmt : m ≤ t := hm ▸ max_le hst ht.1
  have hω : ∀ τ ∈ Ioo m (π / 2 - φ), 0 < cos (τ - s) := fun τ hτ =>
    cos_pos_of_mem_Ioo ⟨by linarith [hτ.1, hs.1], by linarith [hτ.2, hs.1]⟩
  have hd : ∀ τ ∈ Ioo m (π / 2 - φ), HasDerivAt (fun τ => cb s (xKg τ))
      (cos (τ - s) * (Gr τ - Fr τ * tan (τ - s))) τ := by
    intro τ hτ
    have hc := (hω τ hτ).ne'
    refine (hasDerivAt_cb_xKg s τ).congr_deriv ?_
    rw [Real.tan_eq_sin_div_cos, show s - τ = -(τ - s) by ring, sin_neg, cos_neg]
    field_simp
    ring
  have hk : ∀ x ∈ Ioo m (π / 2 - φ), ∀ y ∈ Ioo m (π / 2 - φ), x ≤ y →
      Gr x - Fr x * tan (x - s) < 0 → Gr y - Fr y * tan (y - s) ≤ 0 := by
    intro x hx y hy hxy hkx
    have hxc : x ∈ Icc φ (π / 2 - φ) := ⟨hm2.trans hx.1.le, hx.2.le⟩
    have hyc : y ∈ Icc φ (π / 2 - φ) := ⟨hm2.trans hy.1.le, hy.2.le⟩
    have h1 : Gr y ≤ Gr x := antitoneOn_Gr hxc hyc hxy
    have h2 : Fr x ≤ Fr y := monotoneOn_Fr hxc hyc hxy
    have h3 : tan (x - s) ≤ tan (y - s) :=
      strictMonoOn_tan.monotoneOn ⟨by linarith [hx.1, hs.1], by linarith [hx.2, hs.1]⟩
        ⟨by linarith [hy.1, hs.1], by linarith [hy.2, hs.1]⟩ (by linarith)
    have h4 : 0 ≤ tan (x - s) :=
      tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith [hx.1]) (by linarith [hx.2, hs.1])
    have := mul_le_mul h2 h3 h4 ((Fr_ge_A hyc).trans' A_pos.le)
    linarith
  have hmin := min_le_of_hasDerivAt_mul ((continuous_cb_comp continuous_xKg s).continuousOn)
    hd hω hk t ⟨hmt, ht.2⟩
  have hmv : 0 ≤ cb s (xKg m) := by
    rcases le_total s φ with h | h
    · rw [hm, max_eq_right h]; exact cb_JR_nonneg ⟨hs.1.le, h⟩
    · rw [hm, max_eq_left h, cb_xKg_self]
  have hend : 0 ≤ cb s (xKg (π / 2 - φ)) := by
    rw [← Dg_theta]; exact cb_JL_nonneg ⟨hs.1.le, hst.trans ht.2⟩
  exact le_trans (le_min hmv hend) hmin

/-- **No inner quadrant contains a point of the core.** -/
theorem xKg_not_mem {t s : ℝ} (ht : t ∈ Icc φ (π / 2 - φ)) (hs : s ∈ Ioo 0 (π / 2)) :
    ¬(ca s (xKg t) < 0 ∧ cb s (xKg t) < 0) := by
  rintro ⟨h1, h2⟩
  rcases le_total t s with hts | hst
  · exact absurd h1 (not_lt.2 (ca_xKg_nonneg ht hs hts))
  · exact absurd h2 (not_lt.2 (cb_xKg_nonneg ht hs hst))

/-- **No inner quadrant contains a point of the right tail** (mirror image of `Dg_not_mem`). -/
theorem Bg_not_mem {t s : ℝ} (ht : t ∈ Icc (π / 2 - θ) (π / 2)) (hs : s ∈ Ioo 0 (π / 2)) :
    ¬(ca s (Bg t) < 0 ∧ cb s (Bg t) < 0) := by
  rw [← refl_Dg, ca_refl, cb_refl]
  rintro ⟨h1, h2⟩
  exact Dg_not_mem ⟨by linarith [ht.2], by linarith [ht.1]⟩
    ⟨by linarith [hs.2], by linarith [hs.1]⟩ ⟨h2, h1⟩

lemma Dg_zero_coord0 : Dg 0 0 = 3 * GerversSofa.x 0 - 2 := by
  simp only [Dg, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, u_coord_zero, v_coord_zero, dp₂,
    sin_zero, cos_zero]
  ring

lemma Dg_zero_coord1 : Dg 0 1 = 0 := by
  simp only [Dg, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, u_coord_one, v_coord_one, dp₂,
    sin_zero, cos_zero, p₂_uniform, y_zero]
  ring

/-- **Left of the arch no inner quadrant reaches the `x`-axis**: `cb s (D 0) ≥ 0`. -/
theorem cb_Dg_zero_nonneg {s : ℝ} (hs : s ∈ Icc 0 (π / 2)) : 0 ≤ cb s (Dg 0) := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  rcases le_total s (π / 2 - φ) with h | h
  · exact cb_Dg_nonneg ⟨le_rfl, by linarith⟩ ⟨hs.1, h⟩
  · rw [cb_eq, Dg_zero_coord0, Dg_zero_coord1, p₂_top h]
    obtain ⟨x01, x02⟩ := x0_bounds
    have h1 := sin_le_one s
    have h2 := sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2])
    nlinarith

/-- **Right of the arch no inner quadrant reaches the `x`-axis**: `ca s (B(π/2)) ≥ 0`. -/
theorem ca_Bg_half_nonneg {s : ℝ} (hs : s ∈ Icc 0 (π / 2)) : 0 ≤ ca s (Bg (π / 2)) := by
  rw [← refl_Dg, sub_self, ca_refl]
  exact cb_Dg_zero_nonneg ⟨by linarith [hs.2], by linarith [hs.1]⟩

end Sofa.GP
