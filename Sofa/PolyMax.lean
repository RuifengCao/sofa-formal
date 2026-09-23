/-
# Sofa/PolyMax.lean — existence of maximum polygon caps (Baek Lemma 3.4.2, Thm 3.4.3)

* `tendsto_areaH_of_tendsto`: `A_Θ(h)` depends continuously on the support values (uniform
  convergence of the three graphs on a fixed window);
* `oω_mem`: for `ω < π/2` every cap contains `o_ω` (Remark 3.4.1);
* Lemma 3.4.2: caps with `A_Θ ≥ 0` (and containing `o_ω`) are uniformly bounded;
* **Theorem 3.4.3**: a maximum polygon cap exists.

STATUS: in progress (2026-09-17, Opus 5).
-/
import Sofa.Hausdorff
import Sofa.PolyBalance

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {ω : ℝ} {Θ : Finset ℝ}

lemma inner_u_pi (p : ℝ²) : ⟪p, u π⟫ = -p 0 := by
  have hupi : u π = -u 0 := by rw [show (π : ℝ) = 0 + π by ring, u_add_pi]
  rw [hupi, inner_neg_right, inner_u_zero]

/-! ## Continuity of `A_Θ` in the support values -/

section Continuity

variable (hP : PolySetup ω Θ)
include hP

/-- The sup of `1 / sin s` over `Θ^⋄`. -/
def invSinSup (ω : ℝ) (Θ : Finset ℝ) : ℝ :=
  (diamondFin ω Θ).sup' (diamondFin_nonempty ω Θ) fun s => (sin s)⁻¹

omit hP in
lemma invSin_le {s : ℝ} (hs : s ∈ diamondFin ω Θ) : (sin s)⁻¹ ≤ invSinSup ω Θ :=
  Finset.le_sup' (fun s => (sin s)⁻¹) hs

lemma invSinSup_pos : 0 < invSinSup ω Θ := by
  obtain ⟨s, hs⟩ := diamondFin_nonempty ω Θ
  exact lt_of_lt_of_le (inv_pos.2 (hP.sin_pos hs)) (invSin_le hs)

/-- Uniform bound for the difference of the three graphs of two support vectors. -/
lemma abs_areaIntegrand_sub_le {h h' : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hd : ∀ s ∈ diamondFin ω Θ, |h' s - h s| ≤ c) (x : ℝ) :
    |areaIntegrand ω Θ hP.nonempty h' x - areaIntegrand ω Θ hP.nonempty h x| ≤
      4 * (c * invSinSup ω Θ) := by
  set C := c * invSinSup ω Θ with hC
  have hC0 : 0 ≤ C := mul_nonneg hc (invSinSup_pos hP).le
  have hline : ∀ s ∈ diamondFin ω Θ, ∀ k : ℝ,
      |lineFn s (h' s - k) x - lineFn s (h s - k) x| ≤ C := by
    intro s hs k
    rw [abs_lineFn_sub_lineFn (hP.sin_pos hs), show h' s - k - (h s - k) = h' s - h s by ring, hC,
      div_eq_mul_inv]
    exact mul_le_mul (hd s hs) (invSin_le hs) (inv_pos.2 (hP.sin_pos hs)).le hc
  have hU : |roofU ω Θ h' x - roofU ω Θ h x| ≤ C :=
    abs_inf'_sub_inf'_le _ fun s hs => by simpa using hline s hs 0
  have hF : |floorF ω h' x - floorF ω h x| ≤ C :=
    abs_sup'_sub_sup'_le _ fun s hs => hline s (mem_diamondFin_of_fan hs) 1
  have hR : |roofR Θ hP.nonempty h' x - roofR Θ hP.nonempty h x| ≤ C :=
    abs_sup'_sub_sup'_le _ fun t ht =>
      (abs_min_sub_min_le_max _ _ _ _).trans (max_le (hline t (mem_diamondFin_of_mem ht) 1)
        (hline (t + π / 2) (add_mem_diamondFin ht) 1))
  have h1 := abs_max_sub_max_le_abs (roofU ω Θ h' x - floorF ω h' x)
    (roofU ω Θ h x - floorF ω h x) 0
  have h2 := abs_max_sub_max_le_abs (roofR Θ hP.nonempty h' x - floorF ω h' x)
    (roofR Θ hP.nonempty h x - floorF ω h x) 0
  have e1 : |roofU ω Θ h' x - floorF ω h' x - (roofU ω Θ h x - floorF ω h x)| ≤ 2 * C := by
    rw [show roofU ω Θ h' x - floorF ω h' x - (roofU ω Θ h x - floorF ω h x) =
      (roofU ω Θ h' x - roofU ω Θ h x) - (floorF ω h' x - floorF ω h x) by ring]
    exact (abs_sub _ _).trans (by linarith)
  have e2 : |roofR Θ hP.nonempty h' x - floorF ω h' x -
      (roofR Θ hP.nonempty h x - floorF ω h x)| ≤ 2 * C := by
    rw [show roofR Θ hP.nonempty h' x - floorF ω h' x -
      (roofR Θ hP.nonempty h x - floorF ω h x) =
      (roofR Θ hP.nonempty h' x - roofR Θ hP.nonempty h x) -
      (floorF ω h' x - floorF ω h x) by ring]
    exact (abs_sub _ _).trans (by linarith)
  unfold areaIntegrand
  set A := max (roofU ω Θ h' x - floorF ω h' x) 0
  set A' := max (roofU ω Θ h x - floorF ω h x) 0
  set B := max (roofR Θ hP.nonempty h' x - floorF ω h' x) 0
  set B' := max (roofR Θ hP.nonempty h x - floorF ω h x) 0
  rw [show A - B - (A' - B') = (A - A') - (B - B') by ring]
  exact (abs_sub _ _).trans (by linarith)

/-- `A_Θ` is continuous in the support values (uniformly on a fixed window). -/
theorem tendsto_areaH_of_tendsto {hs : ℕ → ℝ → ℝ} {h : ℝ → ℝ} {c : ℕ → ℝ}
    (hc0 : ∀ n, 0 ≤ c n)
    (hev : ∀ᶠ n in atTop, (∀ s ∈ diamondFin ω Θ, |hs n s - h s| ≤ c n) ∧ c n ≤ 1)
    (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun n => areaH ω Θ hP.nonempty (hs n)) atTop (𝓝 (areaH ω Θ hP.nonempty h)) := by
  obtain ⟨M, hM0, hM⟩ := exists_window hP h
  have hintg : ∀ n, Integrable (areaIntegrand ω Θ hP.nonempty (hs n)) := fun n =>
    (integrable_posPart_U hP (hs n)).sub (integrable_posPart_R hP (hs n))
  have hinth : Integrable (areaIntegrand ω Θ hP.nonempty h) :=
    (integrable_posPart_U hP h).sub (integrable_posPart_R hP h)
  have hsupph : ∀ x, M ≤ |x| → areaIntegrand ω Θ hP.nonempty h x = 0 := by
    intro x hx
    have := hM h (fun s _ => by simp) x hx
    exact areaIntegrand_eq_zero hP this.1 this.2
  have hbound : ∀ᶠ n in atTop, |areaH ω Θ hP.nonempty (hs n) - areaH ω Θ hP.nonempty h| ≤
      2 * M * (4 * (c n * invSinSup ω Θ)) := by
    filter_upwards [hev] with n hn
    obtain ⟨hcle, hc1⟩ := hn
    have hsupp : ∀ x, M ≤ |x| → areaIntegrand ω Θ hP.nonempty (hs n) x = 0 := by
      intro x hx
      have := hM (hs n) (fun s hsm => (hcle s hsm).trans hc1) x hx
      exact areaIntegrand_eq_zero hP this.1 this.2
    have hdiff : areaH ω Θ hP.nonempty (hs n) - areaH ω Θ hP.nonempty h =
        ∫ x, (areaIntegrand ω Θ hP.nonempty (hs n) x - areaIntegrand ω Θ hP.nonempty h x) := by
      rw [areaH, areaH, ← integral_sub (hintg n) hinth]
    have hzero : ∀ x ∉ Icc (-M) M,
        areaIntegrand ω Θ hP.nonempty (hs n) x - areaIntegrand ω Θ hP.nonempty h x = 0 := by
      intro x hx
      have hx' : M ≤ |x| := by
        by_contra hlt
        exact hx (abs_le.1 (not_le.1 hlt).le)
      rw [hsupp x hx', hsupph x hx', sub_zero]
    have hrestrict : ∫ x, (areaIntegrand ω Θ hP.nonempty (hs n) x -
        areaIntegrand ω Θ hP.nonempty h x) =
        ∫ x in Icc (-M) M, (areaIntegrand ω Θ hP.nonempty (hs n) x -
          areaIntegrand ω Θ hP.nonempty h x) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    rw [hdiff, hrestrict]
    have hle := norm_setIntegral_le_of_norm_le_const (C := 4 * (c n * invSinSup ω Θ))
      (s := Icc (-M) M) (by
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_lt_top)
      (fun x _ => by
        rw [Real.norm_eq_abs]
        exact abs_areaIntegrand_sub_le hP (hc0 n) (fun s hsm => hcle s hsm) x)
    rw [Real.norm_eq_abs] at hle
    refine hle.trans ?_
    rw [Real.volume_real_Icc, max_eq_left (by linarith : (0:ℝ) ≤ M - -M)]
    have : 0 ≤ 4 * (c n * invSinSup ω Θ) :=
      mul_nonneg (by norm_num) (mul_nonneg (hc0 n) (invSinSup_pos hP).le)
    nlinarith
  have hlim : Tendsto (fun n => 2 * M * (4 * (c n * invSinSup ω Θ))) atTop (𝓝 0) := by
    have : Tendsto (fun n => 2 * M * (4 * (c n * invSinSup ω Θ))) atTop
        (𝓝 (2 * M * (4 * (0 * invSinSup ω Θ)))) :=
      ((hc.mul_const (invSinSup ω Θ)).const_mul 4).const_mul (2 * M)
    simpa using this
  have hzero : Tendsto
      (fun n => areaH ω Θ hP.nonempty (hs n) - areaH ω Θ hP.nonempty h) atTop (𝓝 0) :=
    squeeze_zero_norm' (hbound.mono fun n hn => by rw [Real.norm_eq_abs]; exact hn) hlim
  exact tendsto_sub_nhds_zero_iff.1 hzero

end Continuity

/-! ## Remark 3.4.1: for `ω < π/2` every cap contains `o_ω` -/

section Oω

lemma inner_u_decomp_cone {ω : ℝ} (hsω : sin ω ≠ 0) (z : ℝ²) (s : ℝ) :
    ⟪z, u s⟫ = (sin (ω - s) / sin ω) * ⟪z, u 0⟫ + (sin s / sin ω) * ⟪z, u ω⟫ := by
  rw [inner_u_decomp, inner_u_zero, inner_u_decomp, sin_sub]
  field_simp
  ring

lemma inner_u_decomp_cone' {ω : ℝ} (hsω : sin ω ≠ 0) (z : ℝ²) (s : ℝ) :
    ⟪z, u (s + π / 2)⟫ =
      (sin (ω - s) / sin ω) * ⟪z, u (π / 2)⟫ + (sin s / sin ω) * ⟪z, u (ω + π / 2)⟫ := by
  rw [inner_u_decomp, inner_u_decomp, inner_u_decomp, cos_add_pi_div_two, sin_add_pi_div_two,
    cos_add_pi_div_two, sin_add_pi_div_two, cos_pi_div_two, sin_pi_div_two, sin_sub]
  field_simp
  ring

/-- **Remark 3.4.1.** -/
theorem oω_mem (hP : PolySetup ω Θ) {K : Set ℝ²} (hK : IsCap K ω) (hω : ω < π / 2) :
    oω ω ∈ K := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hP.pos], hω⟩
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hP.pos (by linarith [pi_pos])
  set c := (1 - sin ω) / cos ω with hc
  -- the two extreme points
  obtain ⟨p, hpK, hp⟩ := exists_supportFn_eq hK.isCompact hK.nonempty ω
  obtain ⟨q, hqK, hq⟩ := exists_supportFn_eq hK.isCompact hK.nonempty (π / 2)
  rw [hK.supportFn_ω] at hp
  rw [hK.supportFn_pi_div_two] at hq
  have hq1 : q 1 = 1 := by rw [← inner_u_pi_div_two]; exact hq
  have hp1 : p 1 ≤ 1 := (hK.subset_para hpK).1.2
  have hpx : c ≤ ⟪p, u 0⟫ := by
    rw [inner_u_zero, hc, div_le_iff₀ hcω]
    rw [inner_u_decomp] at hp
    nlinarith [mul_le_mul_of_nonneg_right hp1 hsω.le]
  have hqω : ⟪q, u ω⟫ ≤ 1 := (hK.subset_para hqK).2.2
  have hqx : c ≤ ⟪q, u (ω + π / 2)⟫ := by
    rw [inner_u_decomp, cos_add_pi_div_two, sin_add_pi_div_two, hq1, hc, div_le_iff₀ hcω]
    rw [inner_u_decomp, hq1] at hqω
    nlinarith [mul_le_mul_of_nonneg_right hqω hsω.le, sin_sq_add_cos_sq ω]
  have hoω0 : ⟪oω ω, u 0⟫ = c := inner_oω_zero ω
  have hoωω : ⟪oω ω, u ω⟫ = 1 := inner_oω_ω hP
  have hoωπ : ⟪oω ω, u (π / 2)⟫ = 1 := inner_oω_pi_div_two ω
  have hoωl : ⟪oω ω, u (ω + π / 2)⟫ = c := inner_oω_left hP
  rw [hK.mem_iff]
  rintro s ((⟨hs0, hs1⟩ | ⟨hs0, hs1⟩) | hs | hs)
  · -- `s ∈ [0, ω]`
    refine le_trans ?_ (hK.inner_le hpK s)
    rw [inner_u_decomp_cone hsω.ne' (oω ω) s, inner_u_decomp_cone hsω.ne' p s, hoω0, hoωω, hp]
    have hα : 0 ≤ sin (ω - s) / sin ω :=
      div_nonneg (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])) hsω.le
    nlinarith [mul_le_mul_of_nonneg_left hpx hα]
  · -- `s ∈ [π/2, ω + π/2]`
    have hs' : s = (s - π / 2) + π / 2 := by ring
    refine le_trans ?_ (hK.inner_le hqK s)
    rw [hs', inner_u_decomp_cone' hsω.ne' (oω ω) (s - π / 2),
      inner_u_decomp_cone' hsω.ne' q (s - π / 2), hoωπ, hoωl, hq]
    have hβ : 0 ≤ sin (s - π / 2) / sin ω :=
      div_nonneg (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])) hsω.le
    nlinarith [mul_le_mul_of_nonneg_left hqx hβ]
  · rw [hs, hK.supportFn_ω_add_pi, u_add_pi, inner_neg_right, hoωω]
    linarith
  · rw [mem_singleton_iff] at hs
    rw [hs, hK.supportFn_three_pi_div_two, u_three_pi_div_two, inner_neg_right, hoωπ]
    linarith

end Oω

/-! ## Lemma 3.4.2: caps with nonnegative area are uniformly bounded -/

section Bound2

variable (hP : PolySetup ω Θ)
include hP

lemma subset_ball_of_lt {K : Set ℝ²} (hK : IsCap K ω) (hω : ω < π / 2) :
    K ⊆ Metric.closedBall (0 : ℝ²) ((cos ω)⁻¹ + 1) := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hP.pos], hω⟩
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hP.pos (by linarith [pi_pos])
  intro p hp
  rw [mem_closedBall_zero_iff]
  obtain ⟨⟨hy0, hy1⟩, hu0, hu1⟩ := hK.subset_para hp
  rw [inner_u_decomp] at hu0 hu1
  refine norm_le_add_of_abs_coord_le ?_ (abs_le.2 ⟨by linarith, hy1⟩)
  have h1 : p 0 ≤ 1 / cos ω := by
    rw [le_div_iff₀ hcω]
    nlinarith [mul_nonneg hy0 hsω.le]
  have h2 : -(1 / cos ω) ≤ p 0 := by
    rw [← neg_div, div_le_iff₀ hcω]
    nlinarith [mul_le_mul_of_nonneg_right hy1 hsω.le, sin_le_one ω]
  rw [inv_eq_one_div, abs_le]
  exact ⟨h2, h1⟩

omit hP in
lemma floorF_eq_zero {h : ℝ → ℝ} (hω : ω = π / 2) (h2 : h (π / 2) = 1) (x : ℝ) :
    floorF ω h x = 0 := by
  have hval : ∀ s ∈ fanFin ω, lineFn s (h s - 1) x = 0 := by
    intro s hs
    have hs2 : s = π / 2 := by
      rcases mem_fanFin.1 hs with hs' | hs'
      · rw [hs', hω]
      · exact hs'
    rw [hs2, h2, sub_self, lineFn, cos_pi_div_two, sin_pi_div_two]
    ring
  refine le_antisymm ((Finset.sup'_le_iff _ _).2 fun s hs => (hval s hs).le) ?_
  rw [← hval ω (self_mem_fanFin ω)]
  exact Finset.le_sup' (fun s => lineFn s (h s - 1) x) (self_mem_fanFin ω)

/-- Lemma 3.4.2 for `ω = π/2`: the width is bounded in terms of `Θ` alone. -/
theorem width_le_of_area_nonneg (hω : ω = π / 2) {t₁ : ℝ} (ht₁ : t₁ ∈ Θ) {K : Set ℝ²}
    (hK : IsPolyCap ω Θ K) (hA : 0 ≤ polySofaArea ω Θ K) :
    supportFn K 0 + supportFn K π ≤
      max (2 * ((cos t₁)⁻¹ + (sin t₁)⁻¹)) (32 / min (cos t₁ / sin t₁) (sin t₁ / cos t₁)) := by
  set h := supportFn K with hh
  have hst := hP.sin_pos_Θ ht₁
  have hct := hP.cos_pos_Θ ht₁
  set c₁ := (cos t₁)⁻¹ + (sin t₁)⁻¹ with hc₁
  set κ := min (cos t₁ / sin t₁) (sin t₁ / cos t₁) with hκ
  have hκ0 : 0 < κ := lt_min (div_pos hct hst) (div_pos hst hct)
  set d := h 0 + h π with hd
  set xW := (h t₁ - 1) / cos t₁ with hxW
  set xZ := -((h (t₁ + π / 2) - 1) / sin t₁) with hxZ
  set L := xW - xZ with hL
  -- the width is at most `L + c₁`
  have hA0 : h 0 ≤ h t₁ / cos t₁ := by
    rw [hh, supportFn_le_iff hK.1.isCompact hK.1.nonempty]
    intro p hp
    have h1 := hK.1.inner_le hp t₁
    have h2 : (0 : ℝ) ≤ p 1 := (hK.1.subset_fan hp).1
    rw [inner_u_decomp] at h1
    rw [inner_u_zero, le_div_iff₀ hct]
    nlinarith [mul_nonneg h2 hst.le]
  have hAπ : h π ≤ h (t₁ + π / 2) / sin t₁ := by
    rw [hh, supportFn_le_iff hK.1.isCompact hK.1.nonempty]
    intro p hp
    have h1 := hK.1.inner_le hp (t₁ + π / 2)
    have h2 : (0 : ℝ) ≤ p 1 := (hK.1.subset_fan hp).1
    rw [inner_u_decomp, cos_add_pi_div_two, sin_add_pi_div_two] at h1
    rw [inner_u_pi, le_div_iff₀ hst]
    nlinarith [mul_nonneg h2 hct.le]
  have hdL : d ≤ L + c₁ := by
    rw [hd, hL, hxW, hxZ, hc₁]
    have e1 : h t₁ / cos t₁ = (h t₁ - 1) / cos t₁ + (cos t₁)⁻¹ := by
      field_simp
      ring
    have e2 : h (t₁ + π / 2) / sin t₁ = (h (t₁ + π / 2) - 1) / sin t₁ + (sin t₁)⁻¹ := by
      field_simp
      ring
    rw [e1] at hA0
    rw [e2] at hAπ
    linarith
  have hdnn : 0 ≤ d := by
    obtain ⟨p, hp⟩ := hK.1.nonempty
    have h1 := hK.1.inner_le hp 0
    have h2 := hK.1.inner_le hp π
    rw [inner_u_zero] at h1
    rw [inner_u_pi] at h2
    rw [← hh] at h1 h2
    rw [hd]
    linarith
  -- the cap has area at most `d`
  have hfloor : ∀ x, floorF ω h x = 0 := fun x => by
    refine floorF_eq_zero hω ?_ x
    rw [hh, ← hω]
    exact hK.1.supportFn_ω
  have hposU : posU ω Θ h = Ioo (-(h π)) (h 0) := by
    have hEq := posU_eq_Ioo hP hK
    rw [hh, hEq, show ω + π / 2 = π by rw [hω]; ring, hω, sin_pi_div_two, mul_one]
  have hcapvol : volume.real (capH ω Θ h) ≤ d := by
    rw [measureReal_capH hP]
    have hzero : ∀ x ∉ posU ω Θ h, max (roofU ω Θ h x - floorF ω h x) 0 = 0 := by
      intro x hx
      have : roofU ω Θ h x ≤ floorF ω h x := not_lt.1 hx
      exact max_eq_right (by linarith)
    have hres : ∫ x, max (roofU ω Θ h x - floorF ω h x) 0 =
        ∫ x in posU ω Θ h, max (roofU ω Θ h x - floorF ω h x) 0 :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    have hbd : ∀ x ∈ posU ω Θ h, ‖max (roofU ω Θ h x - floorF ω h x) 0‖ ≤ 1 := by
      intro x _
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), hfloor, sub_zero]
      refine max_le ?_ zero_le_one
      refine le_trans (Finset.inf'_le _ (mem_diamondFin_of_fan (pi_div_two_mem_fanFin ω))) ?_
      rw [lineFn, cos_pi_div_two, sin_pi_div_two, mul_zero, sub_zero, div_one, hh, ← hω]
      exact le_of_eq hK.1.supportFn_ω
    have hfin : volume (posU ω Θ h) < ⊤ := lt_top_iff_ne_top.2 (volume_posU_ne_top hP h)
    have hle := norm_setIntegral_le_of_norm_le_const (C := 1) hfin hbd
    rw [Real.norm_eq_abs] at hle
    rw [hres]
    refine le_trans (le_abs_self _) (le_trans hle ?_)
    rw [hposU, Real.volume_real_Ioo, one_mul, hd]
    rcases le_or_gt (h 0 - -(h π)) 0 with hle' | hlt'
    · rw [max_eq_right hle']
      linarith
    · rw [max_eq_left hlt'.le]
      linarith
  -- the niche has area at least `κ L² / 8`
  have hnichevol : ∀ hL0 : 0 < L, κ * L ^ 2 / 8 ≤ volume.real (nicheH ω Θ hP.nonempty h) := by
    intro hL0
    set a := xZ + L / 4 with ha
    set b := xW - L / 4 with hb
    have hab : b - a = L / 2 := by rw [ha, hb, hL]; ring
    set c₀ := κ * (L / 4) with hc₀
    have hc₀0 : 0 ≤ c₀ := mul_nonneg hκ0.le (by linarith)
    have hlow : ∀ x ∈ Icc a b, c₀ ≤ max (roofR Θ hP.nonempty h x - floorF ω h x) 0 := by
      rintro x ⟨hx1, hx2⟩
      refine le_trans ?_ (le_max_left _ _)
      rw [hfloor, sub_zero]
      refine le_trans ?_ (Finset.le_sup' (fun t => min (lineFn t (h t - 1) x)
        (lineFn (t + π / 2) (h (t + π / 2) - 1) x)) ht₁)
      refine le_min ?_ ?_
      · have e : lineFn t₁ (h t₁ - 1) x = (xW - x) * (cos t₁ / sin t₁) := by
          rw [lineFn, hxW]
          field_simp
        rw [e, hc₀]
        have h1 : L / 4 ≤ xW - x := by rw [hb] at hx2; linarith
        have h2 : κ ≤ cos t₁ / sin t₁ := min_le_left _ _
        nlinarith [hκ0.le, div_pos hct hst]
      · have e : lineFn (t₁ + π / 2) (h (t₁ + π / 2) - 1) x = (x - xZ) * (sin t₁ / cos t₁) := by
          rw [lineFn, cos_add_pi_div_two, sin_add_pi_div_two, hxZ]
          field_simp
          ring
        rw [e, hc₀]
        have h1 : L / 4 ≤ x - xZ := by rw [ha] at hx1; linarith
        have h2 : κ ≤ sin t₁ / cos t₁ := min_le_right _ _
        nlinarith [hκ0.le, div_pos hst hct]
    have hintR := integrable_posPart_R hP h
    have h1 : (∫ _x in Icc a b, c₀) ≤
        ∫ x in Icc a b, max (roofR Θ hP.nonempty h x - floorF ω h x) 0 := by
      refine setIntegral_mono_on (integrableOn_const measure_Icc_lt_top.ne)
        hintR.integrableOn measurableSet_Icc hlow
    have h2 : (∫ x in Icc a b, max (roofR Θ hP.nonempty h x - floorF ω h x) 0) ≤
        ∫ x, max (roofR Θ hP.nonempty h x - floorF ω h x) 0 :=
      setIntegral_le_integral hintR (Eventually.of_forall fun x => le_max_right _ _)
    rw [measureReal_nicheH hP]
    refine le_trans ?_ (le_trans h1 h2)
    rw [setIntegral_const, Real.volume_real_Icc, max_eq_left (by linarith : (0:ℝ) ≤ b - a), hab,
      smul_eq_mul, hc₀]
    nlinarith [hκ0.le]
  -- combine
  have harea : volume.real (nicheH ω Θ hP.nonempty h) ≤ volume.real (capH ω Θ h) := by
    have := hA
    rw [polySofaArea_eq_areaH hP hK.1, ← hh, areaH_eq hP] at this
    linarith
  rcases le_or_gt d (2 * c₁) with hcase | hcase
  · exact le_trans hcase (le_max_left _ _)
  · have hL0 : 0 < L := by
      have : 0 ≤ c₁ := by
        rw [hc₁]
        positivity
      linarith
    have hkey := hnichevol hL0
    have hdle : κ * L ^ 2 / 8 ≤ d := le_trans hkey (le_trans harea hcapvol)
    have hLd : d / 2 ≤ L := by linarith
    have hd0 : 0 < d := by
      have : 0 ≤ c₁ := by rw [hc₁]; positivity
      linarith
    have : κ * (d / 2) ^ 2 / 8 ≤ κ * L ^ 2 / 8 := by
      have := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ d / 2) hLd 2
      nlinarith [hκ0.le]
    have hfinal : d ≤ 32 / κ := by
      rw [le_div_iff₀ hκ0]
      nlinarith [hd0]
    exact le_trans hfinal (le_max_right _ _)

omit hP in
/-- A uniform ball containing every polygon cap with `o_ω ∈ K` and `A_Θ(K) ≥ 0`; the radius
depends only on `ω` and one angle `t₁`, not on the angle set. -/
theorem exists_ball {t₁ : ℝ} (_hω0 : 0 < ω) (hω1 : ω ≤ π / 2) (ht0 : 0 < t₁) (htω : t₁ < ω) :
    ∃ R : ℝ, 0 < R ∧ ∀ (Θ' : Finset ℝ) (_hP' : PolySetup ω Θ'), t₁ ∈ Θ' → ∀ K : Set ℝ²,
      IsPolyCap ω Θ' K → oω ω ∈ K → 0 ≤ polySofaArea ω Θ' K →
        K ⊆ Metric.closedBall (0 : ℝ²) R := by
  have hst : 0 < sin t₁ :=
    sin_pos_of_pos_of_lt_pi ht0 (by linarith [pi_pos])
  have hct : 0 < cos t₁ :=
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  by_cases hω : ω = π / 2
  · set B := max (2 * ((cos t₁)⁻¹ + (sin t₁)⁻¹))
      (32 / min (cos t₁ / sin t₁) (sin t₁ / cos t₁)) with hB
    have hB0 : 0 ≤ B := le_trans (by positivity) (le_max_left _ _)
    refine ⟨B + 1, by linarith, fun Θ' hP' ht₁ K hK ho hA => ?_⟩
    have hwidth := width_le_of_area_nonneg hP' hω ht₁ hK hA
    have hoω0 : oω ω 0 = 0 := by rw [oω, pt_zero, hω, cos_pi_div_two, div_zero]
    have h0 : (0 : ℝ) ≤ supportFn K 0 := by
      have hle := hK.1.inner_le ho 0
      rw [inner_u_zero, hoω0] at hle
      exact hle
    have hπ : (0 : ℝ) ≤ supportFn K π := by
      have hle := hK.1.inner_le ho π
      rw [inner_u_pi, hoω0, neg_zero] at hle
      exact hle
    intro p hp
    rw [mem_closedBall_zero_iff]
    have hy : 0 ≤ p 1 ∧ p 1 ≤ 1 := (hK.1.subset_para hp).1
    have hx1 : p 0 ≤ supportFn K 0 := by
      have := hK.1.inner_le hp 0
      rwa [inner_u_zero] at this
    have hx2 : -p 0 ≤ supportFn K π := by
      have hle := hK.1.inner_le hp π
      rwa [inner_u_pi] at hle
    refine norm_le_add_of_abs_coord_le (abs_le.2 ⟨by linarith, by linarith⟩)
      (abs_le.2 ⟨by linarith [hy.1], hy.2⟩)
  · refine ⟨(cos ω)⁻¹ + 1, ?_, fun Θ' hP' _ K hK _ _ => subset_ball_of_lt hP' hK.1
      (lt_of_le_of_ne hω1 hω)⟩
    have : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], lt_of_le_of_ne hω1 hω⟩
    positivity

end Bound2

/-! ## Theorem 3.4.3: existence of a maximum polygon cap -/

section Exists

variable (hP : PolySetup ω Θ)
include hP

/-- `⟪o_ω, u_s⟫ ≤ 1` for every `s ∈ Θ^⋄`. -/
lemma inner_oω_le_one {s : ℝ} (hs : s ∈ diamondFin ω Θ) : ⟪oω ω, u s⟫ ≤ 1 := by
  have hω0 := hP.pos
  have hω1 := hP.le
  have hsω : 0 ≤ sin ω := sin_nonneg_of_nonneg_of_le_pi hω0.le (by linarith [pi_pos])
  have hcω : 0 ≤ cos ω := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hω1⟩
  have hc0 : 0 ≤ (1 - sin ω) / cos ω := by
    rcases eq_or_lt_of_le hcω with hcc | hcc
    · rw [← hcc, div_zero]
    · exact div_nonneg (by linarith [sin_le_one ω]) hcc.le
  rcases mem_diamondFin.1 hs with hsΘ | ⟨t, ht, rfl⟩ | hsf
  · -- `s ∈ Θ`
    obtain ⟨hs0, hsω'⟩ := hP.mem_Θ hsΘ
    have hcs : 0 < cos s := hP.cos_pos_Θ hsΘ
    have hss : 0 < sin s := hP.sin_pos_Θ hsΘ
    rcases eq_or_lt_of_le hω1 with hωπ | hωπ
    · -- `ω = π/2`: then `o_ω = (0, 1)`
      rw [inner_u_decomp, oω, pt_zero, pt_one, one_mul, hωπ, cos_pi_div_two, div_zero,
        zero_mul, zero_add]
      exact sin_le_one s
    · have hcωpos : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hωπ⟩
      have hsinle : sin s ≤ sin ω := by
        have := sin_lt_sin_of_lt_of_le_pi_div_two (x := s) (y := ω)
          (by linarith [pi_pos]) hω1 hsω'
        linarith
      have key : (1 - sin ω) * cos s ≤ (1 - sin s) * cos ω := by
        have h1 : 0 ≤ (1 - sin ω) * cos s := mul_nonneg (by linarith [sin_le_one ω]) hcs.le
        have h2 : 0 ≤ (1 - sin s) * cos ω := mul_nonneg (by linarith [sin_le_one s]) hcωpos.le
        have e1 : cos s ^ 2 = 1 - sin s ^ 2 := by nlinarith [sin_sq_add_cos_sq s]
        have e2 : cos ω ^ 2 = 1 - sin ω ^ 2 := by nlinarith [sin_sq_add_cos_sq ω]
        have hsq : ((1 - sin ω) * cos s) ^ 2 ≤ ((1 - sin s) * cos ω) ^ 2 := by
          rw [mul_pow, mul_pow, e1, e2]
          nlinarith [mul_nonneg (mul_nonneg (by linarith [sin_le_one ω] : (0:ℝ) ≤ 1 - sin ω)
            (by linarith [sin_le_one s] : (0:ℝ) ≤ 1 - sin s))
            (by linarith : (0:ℝ) ≤ sin ω - sin s)]
        nlinarith [hsq, h1, h2]
      have hdiv : (1 - sin ω) / cos ω * cos s ≤ 1 - sin s := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hcωpos]
        linarith [key]
      rw [inner_u_decomp, oω, pt_zero, pt_one, one_mul]
      linarith [hdiv]
  · -- `s = t + π/2`
    have hct : 0 ≤ cos t := (hP.cos_pos_Θ ht).le
    have hst : 0 ≤ sin t := (hP.sin_pos_Θ ht).le
    have hA : 0 ≤ (1 - sin ω) / cos ω * sin t := mul_nonneg hc0 hst
    rw [inner_u_decomp, oω, pt_zero, pt_one, one_mul, cos_add_pi_div_two, sin_add_pi_div_two,
      show (1 - sin ω) / cos ω * -sin t = -((1 - sin ω) / cos ω * sin t) by ring]
    linarith [cos_le_one t]
  · -- `s ∈ {ω, π/2}`
    rcases mem_fanFin.1 hsf with hs' | hs' <;> rw [hs']
    · exact le_of_eq (inner_oω_ω hP)
    · exact le_of_eq (inner_oω_pi_div_two ω)

/-- The polygon cap with all support values equal to `1` has an empty niche. -/
lemma nicheH_one_eq_empty : nicheH ω Θ hP.nonempty (fun _ => 1) = ∅ := by
  ext p
  simp only [mem_empty_iff_false, iff_false]
  intro hp
  obtain ⟨hlow, t, ht, h1, h2⟩ := (mem_nicheH_iff hP).1 hp
  have hy : (0 : ℝ) ≤ p 1 := by
    have := hlow (π / 2) (pi_div_two_mem_fanFin ω)
    rwa [inner_u_pi_div_two, sub_self] at this
  have hst := hP.sin_pos_Θ ht
  have hct := hP.cos_pos_Θ ht
  have hdec := coord_one_decomp p t
  rw [← u_add_pi_div_two] at hdec
  simp only [sub_self] at h1 h2
  nlinarith [mul_pos hst (neg_pos.2 h1), mul_pos hct (neg_pos.2 h2)]

/-- The starting polygon cap `K₁` (all support values `1`). -/
theorem isPolyCap_one : IsPolyCap ω Θ (capH ω Θ (fun _ => 1)) := by
  have hoω : oω ω ∈ capH ω Θ (fun _ => 1) := by
    refine (mem_capH_iff hP).2 ⟨fun s hs => ?_, fun s hs => inner_oω_le_one hP hs⟩
    rw [sub_self]
    rcases mem_fanFin.1 hs with hs' | hs' <;> rw [hs']
    · rw [inner_oω_ω hP]; norm_num
    · rw [inner_oω_pi_div_two]; norm_num
  have hzero : (0 : ℝ²) ∈ capH ω Θ (fun _ => 1) := by
    refine (mem_capH_iff hP).2 ⟨fun s hs => ?_, fun s hs => ?_⟩ <;>
      rw [inner_zero_left] <;> norm_num
  refine isPolyCap_capH hP rfl rfl (fun s hs => ?_) (fun s hs => ?_)
  · refine ⟨oω ω, hoω, ?_⟩
    rcases mem_fanFin.1 hs with hs' | hs' <;> rw [hs']
    · exact inner_oω_ω hP
    · exact inner_oω_pi_div_two ω
  · exact ⟨0, hzero, by rw [inner_zero_left]; norm_num⟩

/-- `A_Θ(K₁) ≥ 0` for the starting polygon cap. -/
lemma polySofaArea_one_nonneg : 0 ≤ polySofaArea ω Θ (capH ω Θ (fun _ => 1)) := by
  set K₁ := capH ω Θ (fun _ => 1) with hK₁def
  have hK₁ : IsPolyCap ω Θ K₁ := isPolyCap_one hP
  have hniche : polyNiche ω Θ K₁ = ∅ := by
    rw [polyNiche_eq_nicheH hP hK₁.1]
    refine subset_antisymm ?_ (empty_subset _)
    rw [← nicheH_one_eq_empty hP]
    refine nicheH_mono hP (fun s hs => ?_) (fun s hs => ?_)
    · exact supportFn_capH_le hP _ hs hK₁.1.nonempty
    · rcases mem_fanFin.1 hs with hs' | hs' <;> rw [hs']
      · exact hK₁.1.supportFn_ω.symm
      · exact hK₁.1.supportFn_pi_div_two.symm
  rw [polySofaArea, hniche, measure_empty, ENNReal.toReal_zero, sub_zero]
  positivity

omit hP in
/-- Every cap touches the two lower fan lines. -/
lemma exists_lower_point {K : Set ℝ²} (hK : IsCap K ω) {s : ℝ} (hs : s ∈ fanFin ω) :
    ∃ p ∈ K, ⟪p, u s⟫ = supportFn K s - 1 := by
  rcases mem_fanFin.1 hs with hs' | hs'
  · obtain ⟨p, hp, hps⟩ := exists_supportFn_eq hK.isCompact hK.nonempty (ω + π)
    refine ⟨p, hp, ?_⟩
    rw [hs', hK.supportFn_ω, hK.supportFn_ω_add_pi, u_add_pi, inner_neg_right] at *
    linarith
  · obtain ⟨p, hp, hps⟩ := exists_supportFn_eq hK.isCompact hK.nonempty (3 * π / 2)
    refine ⟨p, hp, ?_⟩
    rw [hs', hK.supportFn_pi_div_two, hK.supportFn_three_pi_div_two, u_three_pi_div_two,
      inner_neg_right] at *
    linarith

/-- **Theorem 3.4.3.** A maximum polygon cap exists. -/
theorem exists_isMaxPolyCap : ∃ K, IsMaxPolyCap ω Θ K := by
  classical
  obtain ⟨t₁, ht₁⟩ := hP.nonempty
  obtain ⟨R, hR0, hRball'⟩ := exists_ball hP.pos hP.le (hP.mem_Θ ht₁).1 (hP.mem_Θ ht₁).2
  have hRball : ∀ K : Set ℝ², IsPolyCap ω Θ K → oω ω ∈ K → 0 ≤ polySofaArea ω Θ K →
      K ⊆ Metric.closedBall (0 : ℝ²) R := fun K => hRball' Θ hP ht₁ K
  set S : Set ℝ := {A | ∃ K, IsPolyCap ω Θ K ∧ oω ω ∈ K ∧ 0 ≤ polySofaArea ω Θ K ∧
    polySofaArea ω Θ K = A} with hSdef
  -- `S` is nonempty
  have hK₁ : IsPolyCap ω Θ (capH ω Θ (fun _ => 1)) := isPolyCap_one hP
  have hoω₁ : oω ω ∈ capH ω Θ (fun _ => 1) := by
    refine (mem_capH_iff hP).2 ⟨fun s hs => ?_, fun s hs => inner_oω_le_one hP hs⟩
    rw [sub_self]
    rcases mem_fanFin.1 hs with hs' | hs' <;> rw [hs']
    · rw [inner_oω_ω hP]; norm_num
    · rw [inner_oω_pi_div_two]; norm_num
  have hSne : S.Nonempty :=
    ⟨_, capH ω Θ (fun _ => 1), hK₁, hoω₁, polySofaArea_one_nonneg hP, rfl⟩
  -- `S` is bounded above
  have hballfin : volume (Metric.closedBall (0 : ℝ²) R) ≠ ⊤ :=
    (isCompact_closedBall (0 : ℝ²) R).measure_lt_top.ne
  have hbdd : BddAbove S := by
    refine ⟨volume.real (Metric.closedBall (0 : ℝ²) R), fun A hA => ?_⟩
    obtain ⟨K, hK, ho, hA0, rfl⟩ := hA
    have h1 : volume.real (polyCap ω Θ K) ≤ volume.real (Metric.closedBall (0 : ℝ²) R) := by
      refine measureReal_mono ?_ hballfin
      rw [polyCap_eq_capH hP hK.1, capH_supportFn hP hK]
      exact hRball K hK ho hA0
    have h2 : (0 : ℝ) ≤ volume.real (polyNiche ω Θ K) := measureReal_nonneg
    rw [polySofaArea]
    simp only [← measureReal_def]
    linarith
  set A' := sSup S with hA'
  -- a maximizing sequence
  have hseq : ∀ n : ℕ, ∃ K : Set ℝ², IsPolyCap ω Θ K ∧ oω ω ∈ K ∧ 0 ≤ polySofaArea ω Θ K ∧
      A' - 1 / (n + 1) < polySofaArea ω Θ K := by
    intro n
    have hlt : A' - 1 / (n + 1) < A' := by
      have : (0 : ℝ) < 1 / (n + 1) := by positivity
      linarith
    obtain ⟨A, hAS, hAlt⟩ := exists_lt_of_lt_csSup hSne hlt
    obtain ⟨K, hK, ho, hA0, rfl⟩ := hAS
    exact ⟨K, hK, ho, hA0, hAlt⟩
  choose Ks hKs hKo hKA0 hKlt using hseq
  -- Blaschke selection
  obtain ⟨L, φ, hφ, hLc, hLne, hLconv, hLball, hLtend⟩ :=
    exists_tendsto_hausdorffDist (K := Ks) (fun n => (hKs n).1.isCompact)
      (fun n => (hKs n).1.nonempty) (fun n => (hKs n).1.convex)
      (fun n => hRball _ (hKs n) (hKo n) (hKA0 n))
  set h' := supportFn L with hh'
  -- the support values converge
  have hconv : ∀ s : ℝ, Tendsto (fun n => supportFn (Ks (φ n)) s) atTop (𝓝 (h' s)) := by
    intro s
    have hb : ∀ n, |supportFn (Ks (φ n)) s - h' s| ≤ Metric.hausdorffDist (Ks (φ n)) L := fun n =>
      abs_supportFn_sub_le_hausdorffDist (hKs (φ n)).1.isCompact hLc
        (hKs (φ n)).1.nonempty hLne s
    have := squeeze_zero_norm' (Eventually.of_forall fun n => by
      rw [Real.norm_eq_abs]; exact hb n) hLtend
    exact tendsto_sub_nhds_zero_iff.1 this
  -- the limit has the right support values
  have hvals : ∀ s : ℝ, (∀ n, supportFn (Ks (φ n)) s = 1) → h' s = 1 := by
    intro s hs
    have hts := hconv s
    simp only [hs] at hts
    exact tendsto_nhds_unique hts tendsto_const_nhds
  have hvals0 : ∀ s : ℝ, (∀ n, supportFn (Ks (φ n)) s = 0) → h' s = 0 := by
    intro s hs
    have hts := hconv s
    simp only [hs] at hts
    exact tendsto_nhds_unique hts tendsto_const_nhds
  have hω' : h' ω = 1 := hvals ω fun n => (hKs (φ n)).1.supportFn_ω
  have hπ' : h' (π / 2) = 1 := hvals (π / 2) fun n => (hKs (φ n)).1.supportFn_pi_div_two
  have hωπ' : h' (ω + π) = 0 := hvals0 _ fun n => (hKs (φ n)).1.supportFn_ω_add_pi
  have h3π' : h' (3 * π / 2) = 0 := hvals0 _ fun n => (hKs (φ n)).1.supportFn_three_pi_div_two
  -- `L ⊆ capH h'`
  have hLsub : L ⊆ capH ω Θ h' := by
    intro p hp
    refine (mem_capH_iff hP).2 ⟨fun s hs => ?_, fun s hs => le_supportFn hLc hp s⟩
    rcases mem_fanFin.1 hs with hs' | hs' <;> rw [hs']
    · rw [hω', sub_self]
      have hb := le_supportFn hLc hp (ω + π)
      rw [← hh', hωπ', u_add_pi, inner_neg_right] at hb
      linarith
    · rw [hπ', sub_self]
      have hb := le_supportFn hLc hp (3 * π / 2)
      rw [← hh', h3π', u_three_pi_div_two, inner_neg_right] at hb
      linarith
  -- `capH h'` is a polygon cap
  have hpoly : IsPolyCap ω Θ (capH ω Θ h') := by
    refine isPolyCap_capH hP hω' hπ' (fun s hs => ?_) (fun s hs => ?_)
    · obtain ⟨p, hp, hps⟩ := exists_supportFn_eq hLc hLne s
      rw [← hh'] at hps
      exact ⟨p, hLsub hp, hps⟩
    · rcases mem_fanFin.1 hs with hs' | hs'
      · obtain ⟨p, hp, hps⟩ := exists_supportFn_eq hLc hLne (ω + π)
        rw [← hh', hωπ', u_add_pi, inner_neg_right] at hps
        refine ⟨p, hLsub hp, ?_⟩
        rw [hs', hω']
        linarith
      · obtain ⟨p, hp, hps⟩ := exists_supportFn_eq hLc hLne (3 * π / 2)
        rw [← hh', h3π', u_three_pi_div_two, inner_neg_right] at hps
        refine ⟨p, hLsub hp, ?_⟩
        rw [hs', hπ']
        linarith
  -- the areas converge
  have hareaconv : Tendsto (fun n => areaH ω Θ hP.nonempty (supportFn (Ks (φ n)))) atTop
      (𝓝 (areaH ω Θ hP.nonempty h')) := by
    refine tendsto_areaH_of_tendsto hP (c := fun n => min 1 (Metric.hausdorffDist (Ks (φ n)) L))
      (fun n => le_min zero_le_one Metric.hausdorffDist_nonneg) ?_ ?_
    · have hev : ∀ᶠ n in atTop, Metric.hausdorffDist (Ks (φ n)) L ≤ 1 :=
        hLtend.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
      filter_upwards [hev] with n hn
      refine ⟨fun s _ => ?_, min_le_left _ _⟩
      rw [min_eq_right hn]
      exact abs_supportFn_sub_le_hausdorffDist (hKs (φ n)).1.isCompact hLc
        (hKs (φ n)).1.nonempty hLne s
    · have : Tendsto (fun n => min 1 (Metric.hausdorffDist (Ks (φ n)) L)) atTop (𝓝 (min 1 0)) :=
        tendsto_const_nhds.min hLtend
      simpa using this
  -- the limit attains the supremum
  have hAreaKs : ∀ n, polySofaArea ω Θ (Ks (φ n)) = areaH ω Θ hP.nonempty
      (supportFn (Ks (φ n))) := fun n => polySofaArea_eq_areaH hP (hKs (φ n)).1
  have hAlim : Tendsto (fun n => polySofaArea ω Θ (Ks (φ n))) atTop
      (𝓝 (areaH ω Θ hP.nonempty h')) := by
    simpa [hAreaKs] using hareaconv
  have hle : ∀ n, polySofaArea ω Θ (Ks (φ n)) ≤ A' := fun n =>
    le_csSup hbdd ⟨Ks (φ n), hKs (φ n), hKo (φ n), hKA0 (φ n), rfl⟩
  have hge : Tendsto (fun n : ℕ => A' - 1 / (φ n + 1)) atTop (𝓝 A') := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / (φ n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp (hφ.tendsto_atTop)
    simpa using tendsto_const_nhds.sub h1
  have hAeq : areaH ω Θ hP.nonempty h' = A' := by
    refine le_antisymm (le_of_tendsto_of_tendsto' hAlim tendsto_const_nhds hle) ?_
    refine le_of_tendsto_of_tendsto' hge hAlim fun n => (hKlt (φ n)).le
  -- `o_ω` survives in the limit
  have hoL : oω ω ∈ L := by
    have hb : ∀ n, Metric.infDist (oω ω) L ≤ Metric.hausdorffDist (Ks (φ n)) L := fun n =>
      Metric.infDist_le_hausdorffDist_of_mem (hKo (φ n))
        (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded (hKs (φ n)).1.nonempty hLne
          (hKs (φ n)).1.isCompact.isBounded hLc.isBounded)
    have hdist : Tendsto (fun _ : ℕ => Metric.infDist (oω ω) L) atTop (𝓝 0) :=
      squeeze_zero (fun _ => Metric.infDist_nonneg) hb hLtend
    have hz : Metric.infDist (oω ω) L = 0 :=
      tendsto_nhds_unique tendsto_const_nhds hdist
    exact (hLc.isClosed.mem_iff_infDist_zero hLne).2 hz
  -- the maximizer
  refine ⟨capH ω Θ h', hpoly, hLsub hoL, ?_⟩
  -- maximality over all polygon caps
  intro K' hK'
  have hA'ge : polySofaArea ω Θ (capH ω Θ h') ≥ A' := by
    rw [polySofaArea_eq_areaH hP hpoly.1, ← hAeq]
    exact areaH_le_areaH_supportFn hP hω' hπ' hpoly
  rcases lt_or_ge (polySofaArea ω Θ K') 0 with hneg | hnonneg
  · have : 0 ≤ A' := le_csSup hbdd ⟨capH ω Θ (fun _ => 1), hK₁, hoω₁,
      polySofaArea_one_nonneg hP, rfl⟩ |>.trans' (polySofaArea_one_nonneg hP)
    linarith
  · by_cases hωπ : ω = π / 2
    · -- translate horizontally so that the translate contains `o_ω`
      obtain ⟨q, hqK, hq⟩ := exists_supportFn_eq hK'.1.isCompact hK'.1.nonempty (π / 2)
      rw [hK'.1.supportFn_pi_div_two, inner_u_pi_div_two] at hq
      set w : ℝ² := pt (-(q 0)) 0 with hw
      set h'' := transH (supportFn K') w with hh''
      have hwπ : ⟪w, u (π / 2)⟫ = 0 := by rw [inner_u_pi_div_two, hw, pt_one]
      have hwω : ⟪w, u ω⟫ = 0 := by rw [hωπ]; exact hwπ
      have hcapH' : capH ω Θ (supportFn K') = K' := capH_supportFn hP hK'
      have hmem : ∀ p : ℝ², p + w ∈ capH ω Θ h'' ↔ p ∈ K' := by
        intro p
        rw [hh'', capH_transH hP, mem_preimage, add_sub_cancel_right, hcapH']
      have hh''ω : h'' ω = 1 := by
        rw [hh'', transH, hwω, add_zero, hK'.1.supportFn_ω]
      have hh''π : h'' (π / 2) = 1 := by
        rw [hh'', transH, hwπ, add_zero, hK'.1.supportFn_pi_div_two]
      have hAp : ∀ s ∈ fanFin ω, ∃ p ∈ capH ω Θ h'', ⟪p, u s⟫ = h'' s := by
        intro s hs
        obtain ⟨p₀, hp₀, hp₀s⟩ := exists_supportFn_eq hK'.1.isCompact hK'.1.nonempty s
        exact ⟨p₀ + w, (hmem p₀).2 hp₀, by rw [inner_add_left, hp₀s, hh'', transH]⟩
      have hBp : ∀ s ∈ fanFin ω, ∃ p ∈ capH ω Θ h'', ⟪p, u s⟫ = h'' s - 1 := by
        intro s hs
        obtain ⟨p₀, hp₀, hp₀s⟩ := exists_lower_point hK'.1 hs
        refine ⟨p₀ + w, (hmem p₀).2 hp₀, ?_⟩
        rw [inner_add_left, hp₀s, hh'', transH]
        ring
      have hpoly'' : IsPolyCap ω Θ (capH ω Θ h'') := isPolyCap_capH hP hh''ω hh''π hAp hBp
      have hoω'' : oω ω ∈ capH ω Θ h'' := by
        have h0 : (1 - sin ω) / cos ω = 0 := by rw [hωπ, cos_pi_div_two, div_zero]
        have hqw : oω ω = q + w := by
          ext i
          fin_cases i <;> simp [oω, hw, h0, hq]
        rw [hqw]
        exact (hmem q).2 hqK
      have harea'' : areaH ω Θ hP.nonempty h'' = polySofaArea ω Θ K' := by
        rw [hh'', areaH_transH hP, polySofaArea_eq_areaH hP hK'.1]
      have hge'' : polySofaArea ω Θ K' ≤ polySofaArea ω Θ (capH ω Θ h'') := by
        rw [polySofaArea_eq_areaH hP hpoly''.1, ← harea'']
        exact areaH_le_areaH_supportFn hP hh''ω hh''π hpoly''
      have hmem'' : polySofaArea ω Θ (capH ω Θ h'') ∈ S :=
        ⟨capH ω Θ h'', hpoly'', hoω'', le_trans hnonneg hge'', rfl⟩
      have := le_csSup hbdd hmem''
      linarith
    · have hoK' : oω ω ∈ K' := oω_mem hP hK'.1 (lt_of_le_of_ne hP.le hωπ)
      have : polySofaArea ω Θ K' ≤ A' := le_csSup hbdd ⟨K', hK', hoK', hnonneg, rfl⟩
      linarith

end Exists

end Sofa
