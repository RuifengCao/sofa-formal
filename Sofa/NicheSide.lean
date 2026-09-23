/-
# Sofa/NicheSide.lean — Baek §8.1 (`B_K`, `D_K`, Lemmas 8.1.5–8.1.7) and Lemma 8.2.2

* Monotonicity from **right** derivatives (`monotoneOn_Icc_of_rightDeriv_nonneg`): the inner corner
  `x_K` only has one-sided derivatives in general.
* **Lemma 8.1.6** (for injective caps): `⟪x_K(t), u_φ⟫ ≤ h_K(φ) − 1` on `[φ, π/2]`
  (`inner_innerCorner_u_le_right`) and the mirror statement on `[0, π/2 − φ]`; consequently every
  point of `H̆^R_K` outside `H^b_K(t)` lies in the quadrant `Q⁻_K(t)` (`mem_QminusS_right`), and
  dually on the left.
* **Def 8.1.4** `Bset φ K = B_K`, `Dset φ K = D_K`, with the elementary facts of **Lemma 8.1.7**.
* **Lemma 8.2.2** without Green's theorem: the region `conv(B ∪ {W^R_K}) \ B` lies in
  `N(K) ∩ H̆^R_K` (`convexHull_diff_Bset_subset`), and by the tangent-cap formula its area is
  `J(X_B, W^R_K) − J(b_B)`.

STATUS: [PROOF-C-local] round 1 (2026-09-22, Opus 5.5).
-/
import Sofa.TangentCap

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace Interval

namespace Sofa

variable {K : Set ℝ²} {φ : ℝ}

/-! ## Monotonicity from right derivatives -/

theorem monotoneOn_Icc_of_rightDeriv_nonneg {F F' : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn F (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivWithinAt F (F' x) (Ioi x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 ≤ F' x) : MonotoneOn F (Icc a b) := by
  have step : ∀ x ∈ Ioc a b, ∀ y ∈ Icc x b, F x ≤ F y := by
    intro x hx y hy
    exact image_le_of_deriv_right_le_deriv_boundary (f := fun _ => F x) (f' := fun _ => 0)
      (a := x) (b := b) continuousOn_const (fun t _ => hasDerivWithinAt_const _ _ _) le_rfl
      (hc.mono (Icc_subset_Icc hx.1.le le_rfl))
      (fun t ht => (hd t ⟨lt_of_lt_of_le hx.1 ht.1, ht.2⟩).Ici_of_Ioi)
      (fun t ht => hpos t ⟨lt_of_lt_of_le hx.1 ht.1, ht.2⟩) hy
  have base : ∀ y ∈ Icc a b, F a ≤ F y := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with hya | hya
    · rw [hya]
    · have hab : a < b := lt_of_lt_of_le hya hy.2
      have hlim : Tendsto F (𝓝[>] a) (𝓝 (F a)) :=
        (hc a ⟨le_rfl, hab.le⟩).mono_of_mem_nhdsWithin
          (mem_of_superset (Ioo_mem_nhdsGT hab) Ioo_subset_Icc_self)
      refine le_of_tendsto hlim ?_
      filter_upwards [Ioc_mem_nhdsGT hya] with z hz
      exact step z ⟨hz.1, hz.2.trans hy.2⟩ y ⟨hz.2, hy.2⟩
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hx.1 with hxa | hxa
  · rw [← hxa]; exact base y hy
  · exact step x ⟨hxa, hx.2⟩ y ⟨hxy, hy.2⟩

theorem antitoneOn_Icc_of_rightDeriv_nonpos {F F' : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn F (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivWithinAt F (F' x) (Ioi x) x)
    (hneg : ∀ x ∈ Ioo a b, F' x ≤ 0) : AntitoneOn F (Icc a b) := by
  have h := monotoneOn_Icc_of_rightDeriv_nonneg (F := fun x => -F x) (F' := fun x => -F' x)
    hc.neg (fun x hx => (hd x hx).neg) (fun x hx => by linarith [hneg x hx])
  intro x hx y hy hxy
  have := h hx hy hxy
  simp only at this
  linarith

/-! ## Lemma 8.1.6: the inner corner stays outside `H̆^R_K` and `H̆^L_K` -/

lemma hasDerivWithinAt_inner_innerCorner (hK : IsCompact K) (hne : K.Nonempty) (w : ℝ²)
    (t : ℝ) :
    HasDerivWithinAt (fun s => ⟪innerCorner K s, w⟫)
      ((1 - armFp K t) * ⟪u t, w⟫ + (armGp K t - 1) * ⟪v t, w⟫) (Ioi t) t := by
  have h := (hasDerivWithinAt_innerCorner hK hne t).inner (𝕜 := ℝ)
    (hasDerivWithinAt_const t (Ioi t) w)
  refine h.congr_deriv ?_
  rw [inner_zero_right, zero_add, inner_add_left, real_inner_smul_left, real_inner_smul_left]

/-- **Baek Lemma 8.1.6 (1)**, the corner part: `x_K(t) ∉ int H̆^R_K` for `t ∈ [φ^R, π/2]`. -/
theorem IsInjectiveCap.inner_innerCorner_u_le_right (hK : IsInjectiveCap K) {t : ℝ}
    (hφ0 : 0 < φ) (hφt : φ ≤ t) (ht : t ≤ π / 2) :
    ⟪innerCorner K t, u φ⟫ ≤ supportFn K φ - 1 := by
  have hKc := hK.isCap.isCompact
  have hne := hK.isCap.nonempty
  have hanti := antitoneOn_Icc_of_rightDeriv_nonpos (F := fun s => ⟪innerCorner K s, u φ⟫)
    (F' := fun s => (1 - armFp K s) * ⟪u s, u φ⟫ + (armGp K s - 1) * ⟪v s, u φ⟫)
    (a := φ) (b := π / 2)
    ((continuous_innerCorner hKc hne).inner continuous_const).continuousOn
    (fun s _ => hasDerivWithinAt_inner_innerCorner hKc hne (u φ) s)
    (fun s hs => by
      obtain ⟨hf, hg⟩ := hK.one_lt_arm s ⟨by linarith [hs.1], hs.2⟩
      rw [inner_u_u_eq_cos, inner_v_u_eq_sin]
      have h1 : 0 < cos (s - φ) :=
        cos_pos_of_mem_Ioo ⟨by linarith [hs.1, pi_pos], by linarith [hs.2]⟩
      have h2 : sin (φ - s) < 0 := by
        rw [show φ - s = -(s - φ) by ring, sin_neg]
        linarith [sin_pos_of_pos_of_lt_pi (x := s - φ) (by linarith [hs.1])
          (by linarith [hs.2, pi_pos])]
      nlinarith)
  have := hanti ⟨le_rfl, by linarith⟩ ⟨hφt, ht⟩ hφt
  simp only at this
  rwa [inner_innerCorner_u] at this

/-- **Baek Lemma 8.1.6 (2)**, the corner part: `x_K(t) ∉ int H̆^L_K` for `t ∈ [0, φ^L]`. -/
theorem IsInjectiveCap.inner_innerCorner_u_le_left (hK : IsInjectiveCap K) {t : ℝ}
    (hφ0 : 0 < φ) (hφ1 : φ < π / 2) (ht0 : 0 ≤ t) (ht : t ≤ π / 2 - φ) :
    ⟪innerCorner K t, u (π - φ)⟫ ≤ supportFn K (π - φ) - 1 := by
  have hKc := hK.isCap.isCompact
  have hne := hK.isCap.nonempty
  have hmono := monotoneOn_Icc_of_rightDeriv_nonneg
    (F := fun s => ⟪innerCorner K s, u (π - φ)⟫)
    (F' := fun s => (1 - armFp K s) * ⟪u s, u (π - φ)⟫ + (armGp K s - 1) * ⟪v s, u (π - φ)⟫)
    (a := 0) (b := π / 2 - φ)
    ((continuous_innerCorner hKc hne).inner continuous_const).continuousOn
    (fun s _ => hasDerivWithinAt_inner_innerCorner hKc hne (u (π - φ)) s)
    (fun s hs => by
      obtain ⟨hf, hg⟩ := hK.one_lt_arm s ⟨hs.1, by linarith [hs.2]⟩
      rw [inner_u_u_eq_cos, inner_v_u_eq_sin]
      have h1 : cos (s - (π - φ)) < 0 := by
        rw [show s - (π - φ) = -(π - φ - s) by ring, cos_neg]
        exact cos_neg_of_pi_div_two_lt_of_lt (by linarith [hs.2]) (by linarith [hs.1, pi_pos])
      have h2 : 0 < sin (π - φ - s) :=
        sin_pos_of_pos_of_lt_pi (by linarith [hs.2]) (by linarith [hs.1])
      nlinarith)
  have := hmono ⟨ht0, ht⟩ ⟨by linarith, le_rfl⟩ ht
  simp only at this
  have e := inner_innerCorner_u_add K (π / 2 - φ)
  rw [show π / 2 - φ + π / 2 = π - φ by ring] at e
  rwa [e] at this

/-- **Lemma 8.1.6 (1)**: a point of `H̆^R_K` outside `H^b_K(t)` (`φ < t ≤ π/2`) is in `Q⁻_K(t)`. -/
theorem IsInjectiveCap.mem_QminusS_right (hK : IsInjectiveCap K) {t : ℝ} (hφ0 : 0 < φ)
    (hφt : φ < t) (ht : t ≤ π / 2) {p : ℝ²} (hpR : supportFn K φ - 1 ≤ ⟪p, u φ⟫)
    (hpt : ⟪p, u t⟫ < supportFn K t - 1) : p ∈ QminusS K t := by
  refine ⟨hpt, ?_⟩
  show ⟪p, u (t + π / 2)⟫ < supportFn K (t + π / 2) - 1
  rw [u_add_pi_div_two]
  by_contra hcon
  rw [not_lt] at hcon
  have hx := hK.inner_innerCorner_u_le_right hφ0 hφt.le ht
  set x := innerCorner K t with hxdef
  have hdec := decomp_u_v t (p - x)
  have hu : ⟪p - x, u t⟫ = ⟪p, u t⟫ - (supportFn K t - 1) := by
    rw [inner_sub_left, hxdef, inner_innerCorner_u]
  have hv : ⟪p - x, v t⟫ = ⟪p, v t⟫ - (supportFn K (t + π / 2) - 1) := by
    rw [inner_sub_left, hxdef, inner_innerCorner_v]
  have key : ⟪p - x, u φ⟫ = ⟪p - x, u t⟫ * cos (t - φ) + ⟪p - x, v t⟫ * sin (φ - t) := by
    conv_lhs => rw [hdec]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u_eq_cos,
      inner_v_u_eq_sin]
  have h1 : 0 < cos (t - φ) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have h2 : sin (φ - t) < 0 := by
    rw [show φ - t = -(t - φ) by ring, sin_neg]
    linarith [sin_pos_of_pos_of_lt_pi (x := t - φ) (by linarith) (by linarith [pi_pos])]
  have hA : ⟪p - x, u t⟫ < 0 := by rw [hu]; linarith
  have hB : 0 ≤ ⟪p - x, v t⟫ := by rw [hv]; linarith
  have h3 : ⟪p - x, u φ⟫ < 0 := by
    rw [key]; nlinarith [mul_neg_of_neg_of_pos hA h1, mul_nonpos_of_nonneg_of_nonpos hB h2.le]
  rw [inner_sub_left] at h3
  linarith

/-- **Lemma 8.1.6 (2)**: a point of `H̆^L_K` outside `H^d_K(t)` (`0 ≤ t < π/2 − φ`) is in
`Q⁻_K(t)`. -/
theorem IsInjectiveCap.mem_QminusS_left (hK : IsInjectiveCap K) {t : ℝ} (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) (ht0 : 0 ≤ t) (ht : t < π / 2 - φ) {p : ℝ²}
    (hpL : supportFn K (π - φ) - 1 ≤ ⟪p, u (π - φ)⟫)
    (hpt : ⟪p, u (t + π / 2)⟫ < supportFn K (t + π / 2) - 1) : p ∈ QminusS K t := by
  refine ⟨?_, hpt⟩
  show ⟪p, u t⟫ < supportFn K t - 1
  rw [u_add_pi_div_two] at hpt
  by_contra hcon
  rw [not_lt] at hcon
  have hx := hK.inner_innerCorner_u_le_left hφ0 hφ1 ht0 ht.le
  set x := innerCorner K t with hxdef
  have hdec := decomp_u_v t (p - x)
  have hu : ⟪p - x, u t⟫ = ⟪p, u t⟫ - (supportFn K t - 1) := by
    rw [inner_sub_left, hxdef, inner_innerCorner_u]
  have hv : ⟪p - x, v t⟫ = ⟪p, v t⟫ - (supportFn K (t + π / 2) - 1) := by
    rw [inner_sub_left, hxdef, inner_innerCorner_v]
  have key : ⟪p - x, u (π - φ)⟫
      = ⟪p - x, u t⟫ * cos (t - (π - φ)) + ⟪p - x, v t⟫ * sin (π - φ - t) := by
    conv_lhs => rw [hdec]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u_eq_cos,
      inner_v_u_eq_sin]
  have h1 : cos (t - (π - φ)) < 0 := by
    rw [show t - (π - φ) = -(π - φ - t) by ring, cos_neg]
    exact cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [pi_pos])
  have h2 : 0 < sin (π - φ - t) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hA : 0 ≤ ⟪p - x, u t⟫ := by rw [hu]; linarith
  have hB : ⟪p - x, v t⟫ < 0 := by rw [hv]; linarith
  have h3 : ⟪p - x, u (π - φ)⟫ < 0 := by
    rw [key]; nlinarith [mul_nonpos_of_nonneg_of_nonpos hA h1.le, mul_neg_of_neg_of_pos hB h2]
  rw [inner_sub_left] at h3
  linarith

/-! ## Elementary bounds for caps, and the floor points `W^R_K`, `Z^L_K` -/

lemma inner_ptWR_u (φ : ℝ) (K : Set ℝ²) (hc : cos φ ≠ 0) :
    ⟪ptWR φ K, u φ⟫ = supportFn K φ - 1 := by
  rw [ptWR, real_inner_smul_left, inner_u_u_eq_cos, zero_sub, cos_neg]; field_simp

lemma inner_ptWR_u_pi_div_two (φ : ℝ) (K : Set ℝ²) : ⟪ptWR φ K, u (π / 2)⟫ = 0 := by
  rw [ptWR, real_inner_smul_left, inner_u_u_eq_cos, show (0:ℝ) - π / 2 = -(π / 2) by ring,
    cos_neg, cos_pi_div_two, mul_zero]

lemma ptZL_eq_smul (φ : ℝ) (K : Set ℝ²) :
    ptZL φ K = ((1 - supportFn K (π - φ)) / cos φ) • u 0 := by
  rw [ptZL, v_pi_div_two, smul_neg, ← neg_smul, ← neg_div, neg_sub]

lemma inner_ptZL_u (φ : ℝ) (K : Set ℝ²) (hc : cos φ ≠ 0) :
    ⟪ptZL φ K, u (π - φ)⟫ = supportFn K (π - φ) - 1 := by
  rw [ptZL_eq_smul, real_inner_smul_left, inner_u_u_eq_cos, show (0:ℝ) - (π - φ) = -(π - φ) by
    ring, cos_neg, cos_pi_sub]
  field_simp; ring

lemma inner_ptZL_u_pi_div_two (φ : ℝ) (K : Set ℝ²) : ⟪ptZL φ K, u (π / 2)⟫ = 0 := by
  rw [ptZL_eq_smul, real_inner_smul_left, inner_u_u_eq_cos,
    show (0:ℝ) - π / 2 = -(π / 2) by ring, cos_neg, cos_pi_div_two, mul_zero]

section Cap

variable (hK : IsCap K (π / 2))
include hK

/-- On `[0, π/2]`: `h_K(t) ≤ h_K(0) cos t + sin t` (the cap lies in `x ≤ h(0)`, `y ≤ 1`). -/
lemma IsCap.supportFn_le_right {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ π / 2) :
    supportFn K t ≤ supportFn K 0 * cos t + sin t := by
  rw [supportFn_le_iff hK.isCompact hK.nonempty]
  intro p hp
  have h0 := hK.inner_le hp 0
  have h1 := hK.inner_le hp (π / 2)
  rw [hK.supportFn_pi_div_two] at h1
  simp only [inner_eq, u_coord_zero, u_coord_one, cos_zero, sin_zero, mul_one, mul_zero,
    add_zero] at h0
  simp only [inner_eq, u_coord_zero, u_coord_one, cos_pi_div_two, sin_pi_div_two, mul_zero,
    zero_add, mul_one] at h1
  rw [inner_eq, u_coord_zero, u_coord_one]
  have hc : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], ht1⟩
  have hs : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [pi_pos])
  nlinarith [mul_le_mul_of_nonneg_right h0 hc, mul_le_mul_of_nonneg_right h1 hs]

/-- On `[π/2, π]`: `h_K(t + π/2) ≤ h_K(π) sin t + cos t`. -/
lemma IsCap.supportFn_le_left {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ π / 2) :
    supportFn K (t + π / 2) ≤ supportFn K π * sin t + cos t := by
  rw [supportFn_le_iff hK.isCompact hK.nonempty]
  intro p hp
  have h0 := hK.inner_le hp π
  have h1 := hK.inner_le hp (π / 2)
  rw [hK.supportFn_pi_div_two] at h1
  simp only [inner_eq, u_coord_zero, u_coord_one, cos_pi, sin_pi, mul_neg, mul_one, mul_zero,
    add_zero] at h0
  simp only [inner_eq, u_coord_zero, u_coord_one, cos_pi_div_two, sin_pi_div_two, mul_zero,
    zero_add, mul_one] at h1
  rw [u_add_pi_div_two, inner_eq, v_coord_zero, v_coord_one]
  have hc : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], ht1⟩
  have hs : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [pi_pos])
  nlinarith [mul_le_mul_of_nonneg_right h0 hs, mul_le_mul_of_nonneg_right h1 hc]

/-- The bottom edge of a cap: `(x, 0) ∈ K` for `−h_K(π) ≤ x ≤ h_K(0)`. -/
lemma IsCap.floor_mem {x : ℝ} (hx0 : -supportFn K π ≤ x) (hx1 : x ≤ supportFn K 0) :
    x • u 0 ∈ K := by
  have hR := hK.cornerR_mem
  have hL := hK.cornerL_mem
  rcases eq_or_lt_of_le (hx0.trans hx1) with heq | hlt
  · have : x = supportFn K 0 := by linarith
    rw [this]; exact hR
  · have hpos : 0 < supportFn K 0 + supportFn K π := by linarith
    set θ := (x + supportFn K π) / (supportFn K 0 + supportFn K π) with hθ
    have hθ0 : 0 ≤ θ := div_nonneg (by linarith) hpos.le
    have hθ1 : θ ≤ 1 := (div_le_one hpos).2 (by linarith)
    have hmem := hK.convex hL hR (by linarith : 0 ≤ 1 - θ) hθ0 (by ring)
    convert hmem using 1
    have e : (1 - θ) * -supportFn K π + θ * supportFn K 0 = x := by
      rw [hθ]; field_simp; ring
    ext i; fin_cases i
    · simp [u]; linarith
    · simp [u]

lemma IsCap.ptWR_mem (hφ0 : 0 < φ) (hφ1 : φ < π / 2)
    (hwid : 1 ≤ (supportFn K 0 + supportFn K π) * cos φ) : ptWR φ K ∈ K := by
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hφ1⟩
  have hA : supportFn K 0 * cos φ ≤ supportFn K φ := by
    have := hK.inner_le hK.cornerR_mem φ
    rwa [real_inner_smul_left, inner_u_u_eq_cos, zero_sub, cos_neg] at this
  have hup := hK.supportFn_le_right hφ0.le hφ1.le
  rw [add_mul] at hwid
  refine hK.floor_mem ?_ ?_
  · rw [le_div_iff₀ hc]; nlinarith
  · rw [div_le_iff₀ hc]; nlinarith [sin_le_one φ]

lemma IsCap.ptZL_mem (hφ0 : 0 < φ) (hφ1 : φ < π / 2)
    (hwid : 1 ≤ (supportFn K 0 + supportFn K π) * cos φ) : ptZL φ K ∈ K := by
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hφ1⟩
  have hC : supportFn K π * cos φ ≤ supportFn K (π - φ) := by
    have := hK.inner_le hK.cornerL_mem (π - φ)
    rwa [real_inner_smul_left, inner_u_u_eq_cos, show π - (π - φ) = φ by ring] at this
  have hup := hK.supportFn_le_left (t := π / 2 - φ) (by linarith) (by linarith)
  rw [show π / 2 - φ + π / 2 = π - φ by ring, sin_pi_div_two_sub, cos_pi_div_two_sub] at hup
  rw [add_mul] at hwid
  rw [ptZL_eq_smul]
  refine hK.floor_mem ?_ ?_
  · rw [le_div_iff₀ hc]; nlinarith [sin_le_one φ]
  · rw [div_le_iff₀ hc]; nlinarith

end Cap

/-! ## Def 8.1.4: `B_K` and `D_K` -/

lemma cos_three_pi_div_two' : cos (3 * π / 2) = 0 := by
  rw [show (3 : ℝ) * π / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two, neg_zero]


/-- **Baek Def 8.1.4** `B_K = K ∩ ⋂_{t ∈ [φ^R, π/2]} H^b_K(t)`. -/
def Bset (φ : ℝ) (K : Set ℝ²) : Set ℝ² := K ∩ ⋂ t ∈ Icc φ (π / 2), hpGe t (supportFn K t - 1)

/-- **Baek Def 8.1.4** `D_K = K ∩ ⋂_{t ∈ [0, φ^L]} H^d_K(t)`. -/
def Dset (φ : ℝ) (K : Set ℝ²) : Set ℝ² :=
  K ∩ ⋂ t ∈ Icc 0 (π / 2 - φ), hpGe (t + π / 2) (supportFn K (t + π / 2) - 1)

lemma mem_Bset {p : ℝ²} :
    p ∈ Bset φ K ↔ p ∈ K ∧ ∀ t ∈ Icc φ (π / 2), supportFn K t - 1 ≤ ⟪p, u t⟫ := by
  simp only [Bset, hpGe, mem_inter_iff, mem_iInter₂, mem_ofPred_eq]

lemma mem_Dset {p : ℝ²} :
    p ∈ Dset φ K ↔
      p ∈ K ∧ ∀ t ∈ Icc 0 (π / 2 - φ), supportFn K (t + π / 2) - 1 ≤ ⟪p, u (t + π / 2)⟫ := by
  simp only [Dset, hpGe, mem_inter_iff, mem_iInter₂, mem_ofPred_eq]

lemma Bset_subset : Bset φ K ⊆ K := inter_subset_left

lemma Dset_subset : Dset φ K ⊆ K := inter_subset_left

lemma isCompact_Bset (hK : IsCompact K) : IsCompact (Bset φ K) :=
  hK.inter_right (isClosed_biInter fun _ _ => isClosed_hpGe _ _)

lemma isCompact_Dset (hK : IsCompact K) : IsCompact (Dset φ K) :=
  hK.inter_right (isClosed_biInter fun _ _ => isClosed_hpGe _ _)

lemma convex_Bset (hc : Convex ℝ K) : Convex ℝ (Bset φ K) :=
  hc.inter (convex_iInter₂ fun _ _ => convex_hpGe _ _)

lemma convex_Dset (hc : Convex ℝ K) : Convex ℝ (Dset φ K) :=
  hc.inter (convex_iInter₂ fun _ _ => convex_hpGe _ _)

section Cap

variable (hK : IsCap K (π / 2))
include hK

lemma IsCap.cornerR_mem_Bset (hφ0 : 0 ≤ φ) : supportFn K 0 • u 0 ∈ Bset φ K := by
  refine mem_Bset.2 ⟨hK.cornerR_mem, fun t ht => ?_⟩
  have h := hK.supportFn_le_right (by linarith [ht.1]) ht.2
  rw [real_inner_smul_left, inner_u_u_eq_cos, zero_sub, cos_neg]
  linarith [sin_le_one t]

lemma IsCap.cornerL_mem_Dset (hφ0 : 0 ≤ φ) : supportFn K π • u π ∈ Dset φ K := by
  refine mem_Dset.2 ⟨hK.cornerL_mem, fun t ht => ?_⟩
  have h := hK.supportFn_le_left ht.1 (by linarith [ht.2])
  rw [real_inner_smul_left, inner_u_u_eq_cos, show π - (t + π / 2) = π / 2 - t by ring,
    cos_pi_div_two_sub]
  linarith [cos_le_one t]

lemma IsCap.Bset_nonempty (hφ0 : 0 ≤ φ) : (Bset φ K).Nonempty := ⟨_, hK.cornerR_mem_Bset hφ0⟩

lemma IsCap.Dset_nonempty (hφ0 : 0 ≤ φ) : (Dset φ K).Nonempty := ⟨_, hK.cornerL_mem_Dset hφ0⟩

/-- **Lemma 8.1.7 (2)**, the floor: `h_{B_K}(3π/2) = 0`. -/
lemma IsCap.supportFn_Bset_three_pi_div_two (hφ0 : 0 ≤ φ) :
    supportFn (Bset φ K) (3 * π / 2) = 0 := by
  have hBc := isCompact_Bset (φ := φ) hK.isCompact
  have hmem := hK.cornerR_mem_Bset hφ0
  apply le_antisymm
  · have := supportFn_mono hK.isCompact ⟨_, hmem⟩ Bset_subset (3 * π / 2)
    rwa [hK.supportFn_three_pi_div_two] at this
  · have := le_supportFn hBc hmem (3 * π / 2)
    rwa [real_inner_smul_left, inner_u_u_eq_cos, zero_sub, cos_neg, cos_three_pi_div_two',
      mul_zero] at this

/-- **Lemma 8.1.7 (4)**, the floor: `h_{D_K}(3π/2) = 0`. -/
lemma IsCap.supportFn_Dset_three_pi_div_two (hφ0 : 0 ≤ φ) :
    supportFn (Dset φ K) (3 * π / 2) = 0 := by
  have hDc := isCompact_Dset (φ := φ) hK.isCompact
  have hmem := hK.cornerL_mem_Dset hφ0
  apply le_antisymm
  · have := supportFn_mono hK.isCompact ⟨_, hmem⟩ Dset_subset (3 * π / 2)
    rwa [hK.supportFn_three_pi_div_two] at this
  · have := le_supportFn hDc hmem (3 * π / 2)
    rwa [real_inner_smul_left, inner_u_u_eq_cos, show π - 3 * π / 2 = -(π / 2) by ring, cos_neg,
      cos_pi_div_two, mul_zero] at this

/-- **Lemma 8.1.7 (1)**. -/
lemma IsCap.supportFn_add_Bset_le (hφ0 : 0 ≤ φ) {t : ℝ} (ht : t ∈ Icc φ (π / 2)) :
    supportFn K t + supportFn (Bset φ K) (π + t) ≤ 1 := by
  have h : supportFn (Bset φ K) (π + t) ≤ 1 - supportFn K t := by
    rw [supportFn_le_iff (isCompact_Bset hK.isCompact) (hK.Bset_nonempty hφ0)]
    intro p hp
    have := (mem_Bset.1 hp).2 t ht
    rw [add_comm, u_add_pi, inner_neg_right]; linarith
  linarith

/-- **Lemma 8.1.7 (3)**. -/
lemma IsCap.supportFn_add_Dset_le (hφ0 : 0 ≤ φ) {t : ℝ} (ht : t ∈ Icc 0 (π / 2 - φ)) :
    supportFn K (π / 2 + t) + supportFn (Dset φ K) (3 * π / 2 + t) ≤ 1 := by
  have h : supportFn (Dset φ K) (3 * π / 2 + t) ≤ 1 - supportFn K (π / 2 + t) := by
    rw [supportFn_le_iff (isCompact_Dset hK.isCompact) (hK.Dset_nonempty hφ0)]
    intro p hp
    have := (mem_Dset.1 hp).2 t ht
    rw [show 3 * π / 2 + t = (t + π / 2) + π by ring, u_add_pi, inner_neg_right,
      show π / 2 + t = t + π / 2 by ring]
    linarith
  linarith

end Cap

/-! ## Lemma 8.1.7 (2), (4): the equalities at `φ^R` and `φ^L` -/

/-- **Lemma 8.1.7 (2)** at `φ^R`: `h_K(φ) + h_{B_K}(π + φ) = 1`.  Baek's proof uses `N(K) ∩ δK = ∅`
(Thm 2.5.8 (2)), which holds when `N(K) ⊆ K` — true for balanced maximum caps (Thm 3.5.4) but
not part of the definition of `K_i`; we assume it. -/
theorem IsInjectiveCap.supportFn_Bset_phi (hK : IsInjectiveCap K) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) (hWR : ptWR φ K ∈ K) (hN : niche K (π / 2) ⊆ K) :
    supportFn K φ + supportFn (Bset φ K) (π + φ) = 1 := by
  have hcap := hK.isCap
  have hKc := hcap.isCompact
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hφ1⟩
  -- the chord `K ∩ b^R_K`, and its end `p` in the direction `v_φ`
  set S := K ∩ line φ (supportFn K φ - 1) with hS
  have hSc : IsCompact S := hKc.inter_right (isClosed_line _ _)
  have hSne : S.Nonempty := ⟨ptWR φ K, hWR, inner_ptWR_u φ K hc.ne'⟩
  obtain ⟨p, hpS, hpmax⟩ := hSc.exists_isMaxOn hSne
    (show Continuous fun q : ℝ² => ⟪q, v φ⟫ by fun_prop).continuousOn
  have hpK : p ∈ K := hpS.1
  have hpline : ⟪p, u φ⟫ = supportFn K φ - 1 := hpS.2
  have hpB : p ∈ Bset φ K := by
    refine mem_Bset.2 ⟨hpK, fun t ht => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    rcases eq_or_lt_of_le ht.1 with h | hφt
    · rw [← h] at hlt; linarith
    rcases eq_or_lt_of_le ht.2 with h' | ht2
    · rw [h', hcap.supportFn_pi_div_two, sub_self, inner_eq, u_coord_zero, u_coord_one,
        cos_pi_div_two, sin_pi_div_two] at hlt
      have := hcap.coord_one_nonneg hpK
      linarith
    · have hQ := hK.mem_QminusS_right hφ0 hφt ht.2 hpline.ge hlt
      have hopen : IsOpen (QminusS K t) := (isOpen_hpLt _ _).inter (isOpen_hpLt _ _)
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen p hQ
      set q := p + (r / 2) • v φ with hq
      have hqQ : q ∈ QminusS K t := hball (by
        rw [Metric.mem_ball, dist_eq_norm, hq, add_sub_cancel_left, norm_smul, norm_v, mul_one,
          Real.norm_of_nonneg (by linarith)]
        linarith)
      have hq1 : 0 ≤ q 1 := by
        have := hcap.coord_one_nonneg hpK
        rw [hq]
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, v_coord_one]
        nlinarith
      have hqN : q ∈ niche K (π / 2) := by
        refine mem_niche_iff.2 ⟨⟨hq1, ?_⟩, t, ⟨by linarith, ht2⟩, hqQ⟩
        rw [inner_eq, u_coord_zero, u_coord_one, cos_pi_div_two, sin_pi_div_two]; linarith
      have hqS : q ∈ S := by
        refine ⟨hN hqN, ?_⟩
        show ⟪q, u φ⟫ = supportFn K φ - 1
        rw [hq, inner_add_left, real_inner_smul_left, inner_v_u, mul_zero, add_zero, hpline]
      have hle := isMaxOn_iff.1 hpmax q hqS
      rw [hq, inner_add_left, real_inner_smul_left, inner_v_v, mul_one] at hle
      linarith
  have hle := hcap.supportFn_add_Bset_le hφ0.le (t := φ) ⟨le_rfl, hφ1.le⟩
  have hge := le_supportFn (isCompact_Bset hKc) hpB (π + φ)
  rw [add_comm π φ, u_add_pi, inner_neg_right, hpline] at hge
  rw [add_comm π φ] at hle ⊢
  linarith

/-- **Lemma 8.1.7 (4)** at `φ^L`: `h_K(π − φ) + h_{D_K}(2π − φ) = 1` (assuming `N(K) ⊆ K`). -/
theorem IsInjectiveCap.supportFn_Dset_phi (hK : IsInjectiveCap K) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) (hZL : ptZL φ K ∈ K) (hN : niche K (π / 2) ⊆ K) :
    supportFn K (π - φ) + supportFn (Dset φ K) (2 * π - φ) = 1 := by
  have hcap := hK.isCap
  have hKc := hcap.isCompact
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hφ1⟩
  set S := K ∩ line (π - φ) (supportFn K (π - φ) - 1) with hS
  have hSc : IsCompact S := hKc.inter_right (isClosed_line _ _)
  have hSne : S.Nonempty := ⟨ptZL φ K, hZL, inner_ptZL_u φ K hc.ne'⟩
  obtain ⟨p, hpS, hpmax⟩ := hSc.exists_isMaxOn hSne
    (show Continuous fun q : ℝ² => ⟪q, u (π / 2 - φ)⟫ by fun_prop).continuousOn
  have hpK : p ∈ K := hpS.1
  have hpline : ⟪p, u (π - φ)⟫ = supportFn K (π - φ) - 1 := hpS.2
  have hpD : p ∈ Dset φ K := by
    refine mem_Dset.2 ⟨hpK, fun t ht => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    rcases eq_or_lt_of_le ht.1 with h | ht0
    · rw [← h, zero_add, hcap.supportFn_pi_div_two, sub_self, inner_eq, u_coord_zero,
        u_coord_one, cos_pi_div_two, sin_pi_div_two] at hlt
      have := hcap.coord_one_nonneg hpK
      linarith
    rcases eq_or_lt_of_le ht.2 with h' | ht2
    · rw [h', show π / 2 - φ + π / 2 = π - φ by ring] at hlt; linarith
    · have hQ := hK.mem_QminusS_left hφ0 hφ1 ht0.le ht2 hpline.ge hlt
      have hopen : IsOpen (QminusS K t) := (isOpen_hpLt _ _).inter (isOpen_hpLt _ _)
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen p hQ
      set q := p + (r / 2) • u (π / 2 - φ) with hq
      have hqQ : q ∈ QminusS K t := hball (by
        rw [Metric.mem_ball, dist_eq_norm, hq, add_sub_cancel_left, norm_smul, norm_u, mul_one,
          Real.norm_of_nonneg (by linarith)]
        linarith)
      have hq1 : 0 ≤ q 1 := by
        have := hcap.coord_one_nonneg hpK
        rw [hq]
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, u_coord_one, sin_pi_div_two_sub]
        nlinarith
      have hqN : q ∈ niche K (π / 2) := by
        refine mem_niche_iff.2 ⟨⟨hq1, ?_⟩, t, ⟨ht0, by linarith⟩, hqQ⟩
        rw [inner_eq, u_coord_zero, u_coord_one, cos_pi_div_two, sin_pi_div_two]; linarith
      have hqS : q ∈ S := by
        refine ⟨hN hqN, ?_⟩
        show ⟪q, u (π - φ)⟫ = supportFn K (π - φ) - 1
        rw [hq, inner_add_left, real_inner_smul_left, inner_u_u_eq_cos,
          show π / 2 - φ - (π - φ) = -(π / 2) by ring, cos_neg, cos_pi_div_two, mul_zero,
          add_zero, hpline]
      have hle := isMaxOn_iff.1 hpmax q hqS
      rw [hq, inner_add_left, real_inner_smul_left, inner_u_u, mul_one] at hle
      linarith
  have hle := hcap.supportFn_add_Dset_le hφ0.le (t := π / 2 - φ) ⟨by linarith, le_rfl⟩
  rw [show π / 2 + (π / 2 - φ) = π - φ by ring, show 3 * π / 2 + (π / 2 - φ) = 2 * π - φ by ring]
    at hle
  have hge := le_supportFn (isCompact_Dset hKc) hpD (2 * π - φ)
  rw [show 2 * π - φ = (π - φ) + π by ring, u_add_pi, inner_neg_right, hpline] at hge
  rw [show 2 * π - φ = (π - φ) + π by ring] at hle ⊢
  linarith

/-- **Baek Theorem 8.1.8**, the equalities (conditions (3), (5) of Def 8.1.3) for
`(K, B_K, D_K)`. -/
theorem IsInjectiveCap.leq_Bset_Dset (hK : IsInjectiveCap K) (hφ0 : 0 < φ) (hφ1 : φ < π / 2)
    (hwid : 1 ≤ (supportFn K 0 + supportFn K π) * cos φ) (hN : niche K (π / 2) ⊆ K) :
    LEq φ K (Bset φ K) (Dset φ K) where
  B_phi := by
    have := hK.supportFn_Bset_phi hφ0 hφ1 (hK.isCap.ptWR_mem hφ0 hφ1 hwid) hN
    rwa [add_comm π φ] at this ⊢
  B_top := by
    rw [hK.isCap.supportFn_pi_div_two, hK.isCap.supportFn_Bset_three_pi_div_two hφ0.le]; ring
  D_top := by
    rw [hK.isCap.supportFn_pi_div_two, hK.isCap.supportFn_Dset_three_pi_div_two hφ0.le]; ring
  D_phi := hK.supportFn_Dset_phi hφ0 hφ1 (hK.isCap.ptZL_mem hφ0 hφ1 hwid) hN

/-- **Baek Lemma 8.1.4**: `K ∩ H̆^R_K` and `K ∩ H̆^L_K` are disjoint (for `K` wide enough). -/
lemma IsCap.not_mem_right_left (hK : IsCap K (π / 2)) (hφ0 : 0 < φ) (hφ1 : φ < π / 2)
    (hwid2 : 2 + 2 * sin φ < (supportFn K 0 + supportFn K π) * cos φ) {p : ℝ²} (hp : p ∈ K)
    (hR : supportFn K φ - 1 ≤ ⟪p, u φ⟫) (hL : supportFn K (π - φ) - 1 ≤ ⟪p, u (π - φ)⟫) :
    False := by
  have hA : supportFn K 0 * cos φ ≤ supportFn K φ := by
    have := hK.inner_le hK.cornerR_mem φ
    rwa [real_inner_smul_left, inner_u_u_eq_cos, zero_sub, cos_neg] at this
  have hC : supportFn K π * cos φ ≤ supportFn K (π - φ) := by
    have := hK.inner_le hK.cornerL_mem (π - φ)
    rwa [real_inner_smul_left, inner_u_u_eq_cos, show π - (π - φ) = φ by ring] at this
  have h1 := hK.inner_le hp (π / 2)
  rw [hK.supportFn_pi_div_two] at h1
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ0 (by linarith [pi_pos])
  have e : ⟪p, u φ⟫ + ⟪p, u (π - φ)⟫ = 2 * sin φ * ⟪p, u (π / 2)⟫ := by
    simp only [inner_eq, u_coord_zero, u_coord_one, cos_pi_sub, sin_pi_sub, cos_pi_div_two,
      sin_pi_div_two]
    ring
  rw [add_mul] at hwid2
  nlinarith

/-! ## Lemma 8.2.2 without Green's theorem -/

lemma vtx2_eq_ptWR {B : Set ℝ²} (hc : 0 < cos φ)
    (hBφ : supportFn K φ + supportFn B (π + φ) = 1) (hB3 : supportFn B (3 * π / 2) = 0) :
    vtx2 B (π + φ) (3 * π / 2) = ptWR φ K := by
  have u3 : ∀ q : ℝ², ⟪q, u (3 * π / 2)⟫ = -⟪q, u (π / 2)⟫ := fun q => by
    rw [show 3 * π / 2 = π / 2 + π by ring, u_add_pi, inner_neg_right]
  have uπφ : ∀ q : ℝ², ⟪q, u (π + φ)⟫ = -⟪q, u φ⟫ := fun q => by
    rw [add_comm, u_add_pi, inner_neg_right]
  refine eq_of_inner_u_eq_two (a := φ) (b := π / 2) ?_ ?_ ?_
  · rw [sin_pi_div_two_sub]; exact hc.ne'
  · rw [inner_ptWR_u φ K hc.ne']
    have h := inner_vtx2_u_left B (π + φ) (3 * π / 2)
    rw [uπφ] at h; linarith
  · rw [inner_ptWR_u_pi_div_two]
    have h := inner_vtx2_u_right B (a := π + φ) (b := 3 * π / 2) (by
      rw [show 3 * π / 2 - (π + φ) = π / 2 - φ by ring, sin_pi_div_two_sub]; exact hc.ne')
    rw [u3, hB3] at h; linarith

lemma vtx2_eq_ptZL {D : Set ℝ²} (hc : 0 < cos φ)
    (hDφ : supportFn K (π - φ) + supportFn D (2 * π - φ) = 1)
    (hD3 : supportFn D (3 * π / 2) = 0) :
    vtx2 D (3 * π / 2) (2 * π - φ) = ptZL φ K := by
  have u3 : ∀ q : ℝ², ⟪q, u (3 * π / 2)⟫ = -⟪q, u (π / 2)⟫ := fun q => by
    rw [show 3 * π / 2 = π / 2 + π by ring, u_add_pi, inner_neg_right]
  have u2πφ : ∀ q : ℝ², ⟪q, u (2 * π - φ)⟫ = -⟪q, u (π - φ)⟫ := fun q => by
    rw [show 2 * π - φ = (π - φ) + π by ring, u_add_pi, inner_neg_right]
  refine eq_of_inner_u_eq_two (a := π / 2) (b := π - φ) ?_ ?_ ?_
  · rw [show π - φ - π / 2 = π / 2 - φ by ring, sin_pi_div_two_sub]; exact hc.ne'
  · rw [inner_ptZL_u_pi_div_two]
    have h := inner_vtx2_u_left D (3 * π / 2) (2 * π - φ)
    rw [u3, hD3] at h; linarith
  · rw [inner_ptZL_u φ K hc.ne']
    have h := inner_vtx2_u_right D (a := 3 * π / 2) (b := 2 * π - φ) (by
      rw [show 2 * π - φ - 3 * π / 2 = π / 2 - φ by ring, sin_pi_div_two_sub]; exact hc.ne')
    rw [u2πφ] at h; linarith

/-- **Baek Lemma 8.2.2 (right half), the region**: `conv(B_K ∪ {W^R_K}) \ B_K ⊆ N(K) ∩ H̆^R_K`. -/
theorem IsInjectiveCap.convexHull_diff_Bset_subset (hK : IsInjectiveCap K) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) (hWR : ptWR φ K ∈ K) :
    convexHull ℝ (insert (ptWR φ K) (Bset φ K)) \ Bset φ K
      ⊆ niche K (π / 2) ∩ hpGe φ (supportFn K φ - 1) := by
  rintro p ⟨hpC, hpB⟩
  have hcap := hK.isCap
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hφ1⟩
  have hCK : convexHull ℝ (insert (ptWR φ K) (Bset φ K)) ⊆ K :=
    convexHull_min (insert_subset_iff.2 ⟨hWR, Bset_subset⟩) hcap.convex
  have hCR : convexHull ℝ (insert (ptWR φ K) (Bset φ K)) ⊆ hpGe φ (supportFn K φ - 1) := by
    refine convexHull_min (insert_subset_iff.2 ⟨?_, fun q hq => ?_⟩) (convex_hpGe _ _)
    · show supportFn K φ - 1 ≤ ⟪ptWR φ K, u φ⟫
      rw [inner_ptWR_u φ K hc.ne']
    · exact (mem_Bset.1 hq).2 φ ⟨le_rfl, hφ1.le⟩
  have hpK := hCK hpC
  have hpR : supportFn K φ - 1 ≤ ⟪p, u φ⟫ := hCR hpC
  have hex : ∃ t ∈ Icc φ (π / 2), ⟪p, u t⟫ < supportFn K t - 1 := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    exact hpB (mem_Bset.2 ⟨hpK, hcon⟩)
  obtain ⟨t, ht, hpt⟩ := hex
  have hφt : φ < t := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h] at hpt; linarith
    · exact h
  have hp1 : 0 ≤ p 1 := hcap.coord_one_nonneg hpK
  have ht2 : t < π / 2 := by
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h, hcap.supportFn_pi_div_two, sub_self, inner_eq, u_coord_zero, u_coord_one,
        cos_pi_div_two, sin_pi_div_two] at hpt
      linarith
    · exact h
  refine ⟨mem_niche_iff.2 ⟨⟨hp1, ?_⟩, t, ⟨by linarith, ht2⟩,
    hK.mem_QminusS_right hφ0 hφt ht.2 hpR hpt⟩, hpR⟩
  rw [inner_eq, u_coord_zero, u_coord_one, cos_pi_div_two, sin_pi_div_two]; linarith

/-- **Baek Lemma 8.2.2 (left half), the region**: `conv(D_K ∪ {Z^L_K}) \ D_K ⊆ N(K) ∩ H̆^L_K`. -/
theorem IsInjectiveCap.convexHull_diff_Dset_subset (hK : IsInjectiveCap K) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) (hZL : ptZL φ K ∈ K) :
    convexHull ℝ (insert (ptZL φ K) (Dset φ K)) \ Dset φ K
      ⊆ niche K (π / 2) ∩ hpGe (π - φ) (supportFn K (π - φ) - 1) := by
  rintro p ⟨hpC, hpD⟩
  have hcap := hK.isCap
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hφ1⟩
  have hCK : convexHull ℝ (insert (ptZL φ K) (Dset φ K)) ⊆ K :=
    convexHull_min (insert_subset_iff.2 ⟨hZL, Dset_subset⟩) hcap.convex
  have hCL : convexHull ℝ (insert (ptZL φ K) (Dset φ K))
      ⊆ hpGe (π - φ) (supportFn K (π - φ) - 1) := by
    refine convexHull_min (insert_subset_iff.2 ⟨?_, fun q hq => ?_⟩) (convex_hpGe _ _)
    · show supportFn K (π - φ) - 1 ≤ ⟪ptZL φ K, u (π - φ)⟫
      rw [inner_ptZL_u φ K hc.ne']
    · have := (mem_Dset.1 hq).2 (π / 2 - φ) ⟨by linarith, le_rfl⟩
      rwa [show π / 2 - φ + π / 2 = π - φ by ring] at this
  have hpK := hCK hpC
  have hpL : supportFn K (π - φ) - 1 ≤ ⟪p, u (π - φ)⟫ := hCL hpC
  have hex : ∃ t ∈ Icc 0 (π / 2 - φ), ⟪p, u (t + π / 2)⟫ < supportFn K (t + π / 2) - 1 := by
    by_contra hcon
    simp only [not_exists, not_and, not_lt] at hcon
    exact hpD (mem_Dset.2 ⟨hpK, hcon⟩)
  obtain ⟨t, ht, hpt⟩ := hex
  have hp1 : 0 ≤ p 1 := hcap.coord_one_nonneg hpK
  have ht0 : 0 < t := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, zero_add, hcap.supportFn_pi_div_two, sub_self, inner_eq, u_coord_zero,
        u_coord_one, cos_pi_div_two, sin_pi_div_two] at hpt
      linarith
    · exact h
  have ht2 : t < π / 2 - φ := by
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h, show π / 2 - φ + π / 2 = π - φ by ring] at hpt; linarith
    · exact h
  refine ⟨mem_niche_iff.2 ⟨⟨hp1, ?_⟩, t, ⟨ht0, by linarith⟩,
    hK.mem_QminusS_left hφ0 hφ1 ht0.le ht2 hpL hpt⟩, hpL⟩
  rw [inner_eq, u_coord_zero, u_coord_one, cos_pi_div_two, sin_pi_div_two]; linarith

/-- **Baek Lemma 8.2.2 (right half)**: `J(X_B, W^R_K) − J(b_B) ≤ |N(K) ∩ H̆^R_K|`, for
`B = B_K`, without Green's theorem. -/
theorem IsInjectiveCap.le_volumeReal_niche_right (hK : IsInjectiveCap K) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) (hwid : 1 ≤ (supportFn K 0 + supportFn K π) * cos φ)
    (hN : niche K (π / 2) ⊆ K) :
    segJ (vtxP (Bset φ K) (π + φ)) (ptWR φ K) - convJ (Bset φ K) (π + φ) (3 * π / 2)
      ≤ volume.real (niche K (π / 2) ∩ hpGe φ (supportFn K φ - 1)) := by
  have hcap := hK.isCap
  have hKc := hcap.isCompact
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hφ1⟩
  have hWR := hcap.ptWR_mem hφ0 hφ1 hwid
  set B := Bset φ K with hBdef
  have hBc : IsCompact B := isCompact_Bset hKc
  have hBconv : Convex ℝ B := convex_Bset hcap.convex
  have hBne : B.Nonempty := hcap.Bset_nonempty hφ0.le
  have hB3 := hcap.supportFn_Bset_three_pi_div_two (φ := φ) hφ0.le
  have hBφ := hK.supportFn_Bset_phi hφ0 hφ1 hWR hN
  have hW := vtx2_eq_ptWR (K := K) hc hBφ hB3
  have hT := volumeReal_convexHull_insert_vtx2 hBc hBconv hBne (a := π + φ) (b := 3 * π / 2)
    (by linarith) (by linarith)
  rw [hW] at hT
  have u3 : ∀ q : ℝ², ⟪q, u (3 * π / 2)⟫ = -⟪q, u (π / 2)⟫ := fun q => by
    rw [show 3 * π / 2 = π / 2 + π by ring, u_add_pi, inner_neg_right]
  have hWB : ⟪vtxM B (3 * π / 2), u (π / 2)⟫ = 0 := by
    have h := inner_vtxM_u B (3 * π / 2)
    rw [hB3, u3] at h
    linarith
  have hzero : segJ (ptWR φ K) (vtxM B (3 * π / 2)) = 0 :=
    segJ_eq_zero_of_line_zero (inner_ptWR_u_pi_div_two φ K) hWB
  have hCc := isCompact_convexHull_insert hBc hBconv hBne (ptWR φ K)
  have hsub := hK.convexHull_diff_Bset_subset hφ0 hφ1 hWR
  have hfin : volume (niche K (π / 2) ∩ hpGe φ (supportFn K φ - 1)) ≠ ⊤ :=
    measure_ne_top_of_subset (inter_subset_left.trans hN) hKc.measure_lt_top.ne
  have hdiff := measureReal_sdiff (μ := volume) ((subset_insert _ _).trans (subset_convexHull ℝ _))
    hBc.isClosed.measurableSet hCc.measure_lt_top.ne
  calc segJ (vtxP B (π + φ)) (ptWR φ K) - convJ B (π + φ) (3 * π / 2)
      = volume.real (convexHull ℝ (insert (ptWR φ K) B)) - volume.real B := by
        rw [hT, hzero]; ring
    _ = volume.real (convexHull ℝ (insert (ptWR φ K) B) \ B) := hdiff.symm
    _ ≤ _ := measureReal_mono hsub hfin

/-- **Baek Lemma 8.2.2 (left half)**: `J(Z^L_K, Y_D) − J(d_D) ≤ |N(K) ∩ H̆^L_K|`, for `D = D_K`. -/
theorem IsInjectiveCap.le_volumeReal_niche_left (hK : IsInjectiveCap K) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 2) (hwid : 1 ≤ (supportFn K 0 + supportFn K π) * cos φ)
    (hN : niche K (π / 2) ⊆ K) :
    segJ (ptZL φ K) (vtxM (Dset φ K) (2 * π - φ)) - convJ (Dset φ K) (3 * π / 2) (2 * π - φ)
      ≤ volume.real (niche K (π / 2) ∩ hpGe (π - φ) (supportFn K (π - φ) - 1)) := by
  have hcap := hK.isCap
  have hKc := hcap.isCompact
  have hc : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hφ1⟩
  have hZL := hcap.ptZL_mem hφ0 hφ1 hwid
  set D := Dset φ K with hDdef
  have hDc : IsCompact D := isCompact_Dset hKc
  have hDconv : Convex ℝ D := convex_Dset hcap.convex
  have hDne : D.Nonempty := hcap.Dset_nonempty hφ0.le
  have hD3 := hcap.supportFn_Dset_three_pi_div_two (φ := φ) hφ0.le
  have hDφ := hK.supportFn_Dset_phi hφ0 hφ1 hZL hN
  have hZ := vtx2_eq_ptZL (K := K) hc hDφ hD3
  have hT := volumeReal_convexHull_insert_vtx2 hDc hDconv hDne (a := 3 * π / 2) (b := 2 * π - φ)
    (by linarith) (by linarith)
  rw [hZ] at hT
  have u3 : ∀ q : ℝ², ⟪q, u (3 * π / 2)⟫ = -⟪q, u (π / 2)⟫ := fun q => by
    rw [show 3 * π / 2 = π / 2 + π by ring, u_add_pi, inner_neg_right]
  have hZD : ⟪vtxP D (3 * π / 2), u (π / 2)⟫ = 0 := by
    have h := inner_vtxP_u D (3 * π / 2)
    rw [hD3, u3] at h
    linarith
  have hzero : segJ (vtxP D (3 * π / 2)) (ptZL φ K) = 0 :=
    segJ_eq_zero_of_line_zero hZD (inner_ptZL_u_pi_div_two φ K)
  have hCc := isCompact_convexHull_insert hDc hDconv hDne (ptZL φ K)
  have hsub := hK.convexHull_diff_Dset_subset hφ0 hφ1 hZL
  have hfin : volume (niche K (π / 2) ∩ hpGe (π - φ) (supportFn K (π - φ) - 1)) ≠ ⊤ :=
    measure_ne_top_of_subset (inter_subset_left.trans hN) hKc.measure_lt_top.ne
  have hdiff := measureReal_sdiff (μ := volume) ((subset_insert _ _).trans (subset_convexHull ℝ _))
    hDc.isClosed.measurableSet hCc.measure_lt_top.ne
  calc segJ (ptZL φ K) (vtxM D (2 * π - φ)) - convJ D (3 * π / 2) (2 * π - φ)
      = volume.real (convexHull ℝ (insert (ptZL φ K) D)) - volume.real D := by
        rw [hT, hzero]; ring
    _ = volume.real (convexHull ℝ (insert (ptZL φ K) D) \ D) := hdiff.symm
    _ ≤ _ := measureReal_mono hsub hfin

end Sofa
