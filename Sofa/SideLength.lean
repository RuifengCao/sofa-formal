/-
# Sofa/SideLength.lean — horizontal side lengths (Baek §4.1)

* **Def 4.1.1**: `w°_K = inf_{t ∈ (0,ω)} w_K(t)`, `z°_K = inf_{t ∈ (0,ω)} z_K(t)`;
* **Lemma 4.1.1**: `|w°_K − w°_{K'}| ≤ (1 + sec ω) d_H(K, K')`;
* **Theorem 4.1.2** (in the form actually used): a maximum polygon cap with `ω < π/2` contains
  the whole segment `[o_ω − w°_K u₀, o_ω]`;
* **Theorem 4.1.4**: the same for a balanced maximum cap.

The paper states 4.1.2 / 4.1.4 as `w°_K ≤ σ_K(π/2)` with `σ_K` the surface area measure, and
deduces the segment statement from "`o_ω` is the right endpoint of the top edge".  Stating the
conclusion directly as a segment inclusion makes the surface area measure — and with it
Theorem 4.1.3 (weak convergence of `σ_{K_n}`, quoted from Schneider) — unnecessary: the limit
`K_n → K` is taken on the *points* `o_ω − g u₀`, using only that `K` is closed.

STATUS: [PROOF-C-local] round 1 (2026-09-17, Opus 5): compiled in the cloud dev tree, no `sorry`.
-/
import Sofa.BalancedMax
import Sofa.Mirror

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {ω : ℝ} {K : Set ℝ²}

/-! ## Definition 4.1.1 -/

/-- **Def 4.1.1.** `w°_K = inf_{t ∈ (0, ω)} w_K(t)`. -/
def gapWinf (K : Set ℝ²) (ω : ℝ) : ℝ := sInf (gapW K '' Ioo 0 ω)

/-- **Def 4.1.1.** `z°_K = inf_{t ∈ (0, ω)} z_K(t)`. -/
def gapZinf (K : Set ℝ²) (ω : ℝ) : ℝ := sInf ((fun t => gapZ K ω t) '' Ioo 0 ω)

lemma gapWinf_mirror (S : Set ℝ²) (ω : ℝ) : gapWinf (mirror ω '' S) ω = gapZinf S ω := by
  have himg : gapW (mirror ω '' S) '' Ioo 0 ω = (fun t => gapZ S ω t) '' Ioo 0 ω := by
    ext x
    simp only [mem_image, mem_Ioo]
    constructor
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      exact ⟨ω - t, ⟨by linarith, by linarith⟩, (gapW_mirror S ω t).symm⟩
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      refine ⟨ω - t, ⟨by linarith, by linarith⟩, ?_⟩
      rw [gapW_mirror]
      congr 1
      ring
  rw [gapWinf, gapZinf, himg]

lemma bddBelow_gapW_image (hK : IsCap K ω) (hω1 : ω ≤ π / 2) :
    BddBelow (gapW K '' Ioo 0 ω) := by
  refine ⟨0, ?_⟩
  rintro x ⟨t, ht, rfl⟩
  exact (hK.gapW_pos hω1 ht).le

lemma gapWinf_nonneg (hK : IsCap K ω) (hω1 : ω ≤ π / 2) : 0 ≤ gapWinf K ω := by
  refine Real.sInf_nonneg ?_
  rintro x ⟨t, ht, rfl⟩
  exact (hK.gapW_pos hω1 ht).le

lemma gapWinf_le (hK : IsCap K ω) (hω1 : ω ≤ π / 2) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) ω) :
    gapWinf K ω ≤ gapW K t :=
  csInf_le (bddBelow_gapW_image hK hω1) ⟨t, ht, rfl⟩

/-- `w_K(t) → h_K(0)` as `t → ω⁻` (the bottom edge of the cap has length `h_K(0)`). -/
lemma tendsto_gapW (hK : IsCap K ω) (hω0 : 0 < ω) (hω1 : ω < π / 2) :
    Tendsto (gapW K) (𝓝[<] ω) (𝓝 (supportFn K 0)) := by
  have hcosω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hcont : ContinuousAt (gapW K) ω := by
    refine continuousAt_const.sub (ContinuousAt.div ?_ continuous_cos.continuousAt hcosω.ne')
    exact ((continuous_supportFn hK.isCompact hK.nonempty).continuousAt).sub continuousAt_const
  have hval : gapW K ω = supportFn K 0 := by
    rw [gapW, hK.supportFn_ω]; simp
  rw [← hval]
  exact hcont.continuousWithinAt.tendsto

lemma gapWinf_le_supportFn_zero (hK : IsCap K ω) (hω0 : 0 < ω) (hω1 : ω < π / 2) :
    gapWinf K ω ≤ supportFn K 0 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h1 : ∀ᶠ t in 𝓝[<] ω, gapW K t < supportFn K 0 + ε :=
    (tendsto_gapW hK hω0 hω1).eventually (eventually_lt_nhds (by linarith))
  have h2 : ∀ᶠ t in 𝓝[<] ω, 0 < t := nhdsWithin_le_nhds (eventually_gt_nhds hω0)
  obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
  exact le_trans (gapWinf_le hK hω1.le ⟨ht2, ht3⟩) ht1.le

/-! ## Lemma 4.1.1 -/

lemma abs_gapW_sub_gapW_le {K' : Set ℝ²} (hK : IsCap K ω) (hK' : IsCap K' ω) (hω0 : 0 < ω)
    (hω1 : ω < π / 2)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) ω) :
    |gapW K t - gapW K' t| ≤ (1 + (cos ω)⁻¹) * Metric.hausdorffDist K K' := by
  have hcosω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hcost : cos ω ≤ cos t :=
    cos_le_cos_of_nonneg_of_le_pi ht.1.le (by linarith [pi_pos]) ht.2.le
  have hcost0 : 0 < cos t := lt_of_lt_of_le hcosω hcost
  set d := Metric.hausdorffDist K K' with hd
  have hd0 : 0 ≤ d := Metric.hausdorffDist_nonneg
  have h0 := abs_le.1 (abs_supportFn_sub_le_hausdorffDist hK.isCompact hK'.isCompact hK.nonempty
    hK'.nonempty 0)
  have ht' := abs_supportFn_sub_le_hausdorffDist hK.isCompact hK'.isCompact hK.nonempty
    hK'.nonempty t
  have hkey : gapW K t - gapW K' t =
      (supportFn K 0 - supportFn K' 0) - (supportFn K t - supportFn K' t) / cos t := by
    rw [gapW, gapW]; field_simp; ring
  have hq : |(supportFn K t - supportFn K' t) / cos t| ≤ (cos ω)⁻¹ * d := by
    rw [abs_div, abs_of_pos hcost0, show (cos ω)⁻¹ * d = d / cos ω by field_simp]
    exact div_le_div₀ hd0 ht' hcosω hcost
  have aq := abs_le.1 hq
  rw [hkey, abs_le]
  constructor <;> linarith [aq.1, aq.2, h0.1, h0.2]

/-- **Lemma 4.1.1** (the one-sided form that is used): `w°` cannot drop by more than
`(1 + sec ω) d_H`. -/
lemma gapWinf_sub_le_gapWinf {K' : Set ℝ²} (hK : IsCap K ω) (hK' : IsCap K' ω)
    (hω0 : 0 < ω) (hω1 : ω < π / 2) :
    gapWinf K ω - (1 + (cos ω)⁻¹) * Metric.hausdorffDist K K' ≤ gapWinf K' ω := by
  refine le_csInf ⟨gapW K' (ω / 2), ⟨ω / 2, ⟨by linarith, by linarith⟩, rfl⟩⟩ ?_
  rintro x ⟨t, ht, rfl⟩
  have h1 := gapWinf_le hK hω1.le ht
  have h2 := (abs_le.1 (abs_gapW_sub_gapW_le hK hK' hω0 hω1 ht)).2
  linarith

/-! ## The bottom edge in the graph representation -/

section Graph

variable {Θ : Finset ℝ} (hP : PolySetup ω Θ)

omit hP in
lemma lineFn_pi_div_two (c x : ℝ) : lineFn (π / 2) c x = c := by
  rw [lineFn, cos_pi_div_two, sin_pi_div_two]; ring

omit hP in
lemma lineFn_fan_pi_div_two {h : ℝ → ℝ} (h2 : h (π / 2) = 1) (x : ℝ) :
    lineFn (π / 2) (h (π / 2) - 1) x = 0 := by rw [lineFn_pi_div_two, h2]; ring

omit hP in
lemma floorF_nonneg {h : ℝ → ℝ} (h2 : h (π / 2) = 1) (x : ℝ) : 0 ≤ floorF ω h x := by
  have hle := Finset.le_sup' (fun s => lineFn s (h s - 1) x) (pi_div_two_mem_fanFin ω)
  rwa [lineFn_fan_pi_div_two h2] at hle

include hP in
lemma floorF_eq_zero_iff (hω1 : ω < π / 2) {h : ℝ → ℝ} (h1 : h ω = 1) (h2 : h (π / 2) = 1)
    (x : ℝ) : floorF ω h x = 0 ↔ 0 ≤ x := by
  have hsω : 0 < sin ω := hP.sin_pos_fan (self_mem_fanFin ω)
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hP.pos], hω1⟩
  constructor
  · intro hx
    have hle : lineFn ω (h ω - 1) x ≤ 0 := by
      rw [← hx]; exact Finset.le_sup' (fun s => lineFn s (h s - 1) x) (self_mem_fanFin ω)
    rw [h1, lineFn, div_nonpos_iff] at hle
    rcases le_or_gt 0 x with hx0 | hx0
    · exact hx0
    · rcases hle with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> nlinarith
  · intro hx
    refine le_antisymm ?_ (floorF_nonneg h2 x)
    rw [floorF, Finset.sup'_le_iff]
    intro s hs
    rcases mem_fanFin.1 hs with rfl | rfl
    · rw [h1, lineFn, div_nonpos_iff]
      right
      exact ⟨by nlinarith, hsω.le⟩
    · rw [lineFn_fan_pi_div_two h2]

include hP in
lemma actF_pi_div_two (hω1 : ω < π / 2) {h : ℝ → ℝ} (h1 : h ω = 1) (h2 : h (π / 2) = 1) :
    actF ω h (π / 2) = Ici 0 := by
  ext x
  simp only [actF, mem_ofPred_eq, mem_Ici, lineFn_fan_pi_div_two h2]
  exact floorF_eq_zero_iff hP hω1 h1 h2 x

omit hP in
lemma actR_pi_div_two_inter_posR (hΘ : Θ.Nonempty) {h : ℝ → ℝ} (h2 : h (π / 2) = 1) :
    actR Θ hΘ h (π / 2) ∩ posR ω Θ hΘ h = ∅ := by
  ext x
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hx hR
  rw [actR, mem_ofPred_eq, lineFn_fan_pi_div_two h2] at hx
  rw [posR, mem_ofPred_eq, hx] at hR
  linarith [floorF_nonneg (ω := ω) h2 x]

include hP in
lemma Ici_inter_posR_subset (_hω1 : ω < π / 2) (hK : IsPolyCap ω Θ K) :
    Ici (0 : ℝ) ∩ posR ω Θ hP.nonempty (supportFn K) ⊆
      Iio (supportFn K 0 - gapWinf K ω) := by
  rintro x ⟨-, hxR⟩
  rw [posR, mem_ofPred_eq, roofR, Finset.lt_sup'_iff] at hxR
  obtain ⟨t, ht, hlt⟩ := hxR
  have hf := floorF_nonneg (ω := ω) hK.1.supportFn_pi_div_two x
  have h0 : 0 < lineFn t (supportFn K t - 1) x :=
    lt_of_le_of_lt hf (lt_of_lt_of_le hlt (min_le_left _ _))
  have hst := hP.sin_pos_Θ ht
  have hct := hP.cos_pos_Θ ht
  rw [lineFn, lt_div_iff₀ hst] at h0
  have hx : x < (supportFn K t - 1) / cos t := by rw [lt_div_iff₀ hct]; nlinarith
  have hw := gapWinf_le hK.1 hP.le ⟨(hP.mem_Θ ht).1, (hP.mem_Θ ht).2⟩
  rw [gapW] at hw
  simp only [mem_Iio]
  linarith

include hP in
lemma measureReal_Ici_inter_posU (hK : IsPolyCap ω Θ K) (hoω : oω ω ∈ K) :
    volume.real (Ici (0 : ℝ) ∩ posU ω Θ (supportFn K)) = supportFn K 0 := by
  have hsω : 0 < sin ω := hP.sin_pos_fan (self_mem_fanFin ω)
  have hq : 0 ≤ (1 - sin ω) / cos ω := by
    rcases eq_or_lt_of_le hP.le with h | h
    · rw [h, cos_pi_div_two, div_zero]
    · exact div_nonneg (by linarith [sin_le_one ω]) (cos_pos_of_mem_Ioo
        ⟨by linarith [pi_pos, hP.pos], h⟩).le
  have h0 : 0 ≤ supportFn K 0 := by
    have := le_supportFn hK.1.isCompact hoω 0
    rw [inner_oω_zero] at this
    linarith
  have hC : -(supportFn K (ω + π / 2) * sin ω) ≤ 0 := by
    have := le_supportFn hK.1.isCompact hoω (ω + π / 2)
    rw [inner_oω_left hP] at this
    nlinarith
  rw [posU_eq_Ioo hP hK]
  have hfin0 : volume (Ioo (-(supportFn K (ω + π / 2) * sin ω)) (supportFn K 0)) ≠ ⊤ :=
    measure_Ioo_lt_top.ne
  have hfinIcc : volume (Icc (0 : ℝ) (supportFn K 0)) ≠ ⊤ := measure_Icc_lt_top.ne
  have hfin : volume (Ici (0 : ℝ) ∩ Ioo (-(supportFn K (ω + π / 2) * sin ω)) (supportFn K 0))
      ≠ ⊤ := ne_top_of_le_ne_top hfin0 (measure_mono inter_subset_right)
  have hsub1 : Ioo (0 : ℝ) (supportFn K 0) ⊆
      Ici (0 : ℝ) ∩ Ioo (-(supportFn K (ω + π / 2) * sin ω)) (supportFn K 0) := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨hx1.le, ⟨by linarith, hx2⟩⟩
  have hsub2 : Ici (0 : ℝ) ∩ Ioo (-(supportFn K (ω + π / 2) * sin ω)) (supportFn K 0) ⊆
      Icc (0 : ℝ) (supportFn K 0) := fun x hx => ⟨hx.1, hx.2.2.le⟩
  have h1 := measureReal_mono hsub1 hfin
  have h2 := measureReal_mono hsub2 hfinIcc
  rw [Real.volume_real_Ioo_of_le (by linarith)] at h1
  rw [Real.volume_real_Icc_of_le (by linarith)] at h2
  linarith

include hP in
/-- Half of **Theorem 4.1.2**: `w°_K ≤ τ_K(π/2)` (the segment argument of the paper, carried out
on the bottom edge `{x ≥ 0}` of the graph representation). -/
theorem gapWinf_le_tauH (hω1 : ω < π / 2) (hK : IsPolyCap ω Θ K) (hoω : oω ω ∈ K) :
    gapWinf K ω ≤ tauH ω Θ hP.nonempty (supportFn K) (π / 2) := by
  have hw0 := gapWinf_nonneg hK.1 hP.le
  have hwh := gapWinf_le_supportFn_zero hK.1 hP.pos hω1
  have hA : actF ω (supportFn K) (π / 2) = Ici 0 :=
    actF_pi_div_two hP hω1 hK.1.supportFn_ω hK.1.supportFn_pi_div_two
  have hR : actR Θ hP.nonempty (supportFn K) (π / 2) ∩ posR ω Θ hP.nonempty (supportFn K) = ∅ :=
    actR_pi_div_two_inter_posR hP.nonempty hK.1.supportFn_pi_div_two
  have hU : volume.real (Ici (0 : ℝ) ∩ posU ω Θ (supportFn K)) = supportFn K 0 :=
    measureReal_Ici_inter_posU hP hK hoω
  have hsub : Ici (0 : ℝ) ∩ posR ω Θ hP.nonempty (supportFn K) ⊆
      Ico 0 (supportFn K 0 - gapWinf K ω) :=
    fun x hx => ⟨hx.1, Ici_inter_posR_subset hP hω1 hK hx⟩
  have hle : volume.real (Ici (0 : ℝ) ∩ posR ω Θ hP.nonempty (supportFn K)) ≤
      supportFn K 0 - gapWinf K ω := by
    have hfinIco : volume (Ico (0 : ℝ) (supportFn K 0 - gapWinf K ω)) ≠ ⊤ :=
      measure_Ico_lt_top.ne
    refine le_trans (measureReal_mono hsub hfinIco) ?_
    rw [Real.volume_real_Ico_of_le (by linarith)]
    linarith
  rw [tauH, hA, hR, measureReal_empty, sin_pi_div_two, div_one, hU]
  linarith

/-! ## The top edge -/

section TopEdge

omit hP in
lemma le_lineFn_of_mem_Icc {s c y a b x : ℝ} (hs : 0 < sin s) (ha : y ≤ lineFn s c a)
    (hb : y ≤ lineFn s c b) (hx : x ∈ Icc a b) : y ≤ lineFn s c x := by
  rw [lineFn, le_div_iff₀ hs] at ha hb ⊢
  rcases le_or_gt 0 (cos s) with hc | hc
  · nlinarith [hx.2]
  · nlinarith [hx.1]

include hP in
lemma one_le_roofU_of_mem_Icc {h : ℝ → ℝ} {a b x : ℝ} (ha : 1 ≤ roofU ω Θ h a)
    (hb : 1 ≤ roofU ω Θ h b) (hx : x ∈ Icc a b) : 1 ≤ roofU ω Θ h x := by
  rw [roofU, Finset.le_inf'_iff]
  intro s hs
  exact le_lineFn_of_mem_Icc (hP.sin_pos hs)
    (le_trans ha (Finset.inf'_le (fun s => lineFn s (h s) a) hs))
    (le_trans hb (Finset.inf'_le (fun s => lineFn s (h s) b) hs)) hx

omit hP in
lemma roofU_le_one {h : ℝ → ℝ} (h2 : h (π / 2) = 1) (x : ℝ) : roofU ω Θ h x ≤ 1 := by
  have hle := Finset.inf'_le (fun s => lineFn s (h s) x) (mem_diamondFin_of_fan
    (pi_div_two_mem_fanFin ω) (Θ := Θ))
  rwa [lineFn_pi_div_two, h2] at hle

/-- For a cap with `ω < π/2`, `h_K(ω + π/2) ≤ sec ω`. -/
lemma supportFn_left_le (hK : IsCap K ω) (hω0 : 0 < ω) (hω1 : ω < π / 2) :
    supportFn K (ω + π / 2) ≤ (cos ω)⁻¹ := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  rw [supportFn_le_iff hK.isCompact hK.nonempty]
  intro p hp
  obtain ⟨⟨hp0, hp1⟩, hq0, -⟩ := mem_para_iff.1 (hK.subset_para hp)
  rw [inner_u_decomp] at hq0 ⊢
  rw [cos_add_pi_div_two, sin_add_pi_div_two, inv_eq_one_div, le_div_iff₀ hcω]
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  nlinarith [sin_sq_add_cos_sq ω, mul_nonneg hq0 hsω.le]

include hP in
/-- The top edge of a polygon cap containing `o_ω` reaches at least `σ_K(π/2)` to the left of
`o_ω`. -/
theorem pt_one_mem_of_mem_Icc (hω1 : ω < π / 2) (hK : IsPolyCap ω Θ K) (hoω : oω ω ∈ K)
    {x : ℝ} (hx : x ∈ Icc ((1 - sin ω) / cos ω - sigmaH ω Θ (supportFn K) (π / 2))
      ((1 - sin ω) / cos ω)) : pt x 1 ∈ K := by
  classical
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hP.pos], hω1⟩
  have hsω : 0 < sin ω := hP.sin_pos_fan (self_mem_fanFin ω)
  have h1 : supportFn K ω = 1 := hK.1.supportFn_ω
  have h2 : supportFn K (π / 2) = 1 := hK.1.supportFn_pi_div_two
  have hcapH : capH ω Θ (supportFn K) = K := capH_supportFn hP hK
  set b : ℝ := (1 - sin ω) / cos ω with hb
  set xC : ℝ := -(supportFn K (ω + π / 2) * sin ω) with hxC
  have hb0 : 0 ≤ b := div_nonneg (by linarith [sin_le_one ω]) hcω.le
  have hoωzero : (oω ω).ofLp 0 = b := by rw [oω, pt_zero]
  have hoωone : (oω ω).ofLp 1 = 1 := by rw [oω, pt_one]
  -- `-tan ω ≤ xC ≤ 0 ≤ b`
  have hxCle : -(sin ω / cos ω) ≤ xC := by
    have hle := supportFn_left_le hK.1 hP.pos hω1
    have hkey : supportFn K (ω + π / 2) * sin ω ≤ sin ω / cos ω := by
      calc supportFn K (ω + π / 2) * sin ω ≤ (cos ω)⁻¹ * sin ω :=
            mul_le_mul_of_nonneg_right hle hsω.le
        _ = sin ω / cos ω := by rw [div_eq_inv_mul]
    rw [hxC]; linarith
  have hxC0 : xC ≤ 0 := by
    have := le_supportFn hK.1.isCompact hoω (ω + π / 2)
    rw [inner_oω_left hP] at this
    rw [hxC]
    nlinarith
  -- the closed interval `A'` of points where the roof reaches height one
  set A' : Set ℝ := {y | 1 ≤ roofU ω Θ (supportFn K) y} ∩ Icc xC b with hA'
  have hA'closed : IsClosed A' :=
    (isClosed_le continuous_const (continuous_roofU _)).inter isClosed_Icc
  have hbA : 1 ≤ roofU ω Θ (supportFn K) b := by
    have hmem : oω ω ∈ capH ω Θ (supportFn K) := by rw [hcapH]; exact hoω
    have := hmem.2
    rwa [hoωzero, hoωone] at this
  have hbA' : b ∈ A' := ⟨hbA, ⟨by linarith, le_rfl⟩⟩
  have hA'bdd : BddBelow A' := ⟨xC, fun y hy => hy.2.1⟩
  have ha₀ : sInf A' ∈ A' := hA'closed.csInf_mem ⟨b, hbA'⟩ hA'bdd
  have hA'ord : A'.OrdConnected :=
    Set.OrdConnected.inter ⟨fun y hy z hz w hw => one_le_roofU_of_mem_Icc hP hy hz hw⟩
      ordConnected_Icc
  have hIcc : Icc (sInf A') b ⊆ A' := hA'ord.out ha₀ hbA'
  -- the top edge is contained in `A'`
  have hE : actU ω Θ (supportFn K) (π / 2) ∩ posU ω Θ (supportFn K) ⊆ A' := by
    rintro y ⟨hy1, hy2⟩
    rw [actU, mem_ofPred_eq, lineFn_pi_div_two, h2] at hy1
    have hyU : 1 ≤ roofU ω Θ (supportFn K) y := le_of_eq hy1.symm
    have hyf : floorF ω (supportFn K) y ≤ 1 := by
      rw [posU, mem_ofPred_eq] at hy2; linarith [hy1 ▸ hy2]
    have hmem : pt y 1 ∈ K := by
      rw [← hcapH]
      exact ⟨by rw [pt_zero, pt_one]; exact hyf, by rw [pt_zero, pt_one]; exact hyU⟩
    have hpara := mem_para_iff.1 (hK.1.subset_para hmem)
    have hle := hpara.2.2
    rw [inner_u_decomp, pt_zero, pt_one] at hle
    refine ⟨hyU, ⟨(posU_subset_Ioi hP hK hy2).le, ?_⟩⟩
    rw [hb, le_div_iff₀ hcω]
    linarith
  -- hence `σ_K(π/2) ≤ b - sInf A'`
  have hfin : volume (Icc (sInf A') b) ≠ ⊤ := measure_Icc_lt_top.ne
  have hσ : sigmaH ω Θ (supportFn K) (π / 2) ≤ b - sInf A' := by
    have hsub : actU ω Θ (supportFn K) (π / 2) ∩ posU ω Θ (supportFn K) ⊆ Icc (sInf A') b :=
      fun y hy => ⟨csInf_le hA'bdd (hE hy), (hE hy).2.2⟩
    have hmono := measureReal_mono hsub hfin
    rw [Real.volume_real_Icc_of_le (ha₀.2.2)] at hmono
    rw [sigmaH, sin_pi_div_two, div_one]
    exact hmono
  -- conclude
  have hxA' : x ∈ A' := hIcc ⟨by linarith [hx.1], hx.2⟩
  rw [← hcapH]
  refine ⟨?_, ?_⟩
  · rw [pt_zero, pt_one, floorF, Finset.sup'_le_iff]
    intro s hs
    rcases mem_fanFin.1 hs with rfl | rfl
    · rw [h1, lineFn, div_le_iff₀ hsω]
      have hxge : -(sin _ / cos _) ≤ x := le_trans hxCle hxA'.2.1
      have h3 := mul_le_mul_of_nonneg_right hxge hcω.le
      rw [neg_mul, div_mul_cancel₀ _ hcω.ne'] at h3
      linarith
    · rw [lineFn_fan_pi_div_two h2]; norm_num
  · rw [pt_zero, pt_one]; exact hxA'.1

include hP in
/-- **Theorem 4.1.2.** A maximum polygon cap with `ω < π/2` contains the whole segment
`[o_ω − w°_K u₀, o_ω]` of its top edge. -/
theorem IsMaxPolyCap.mem_top_segment (hω1 : ω < π / 2) (hK : IsMaxPolyCap ω Θ K)
    {g : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ gapWinf K ω) :
    pt ((1 - sin ω) / cos ω - g) 1 ∈ K := by
  have hbal := IsMaxPolyCap.balanced hP hK
    (mem_diamondFin_of_fan (pi_div_two_mem_fanFin ω) (Θ := Θ))
  have hτ := gapWinf_le_tauH hP hω1 hK.1 hK.2.1
  refine pt_one_mem_of_mem_Icc hP hω1 hK.1 hK.2.1 ⟨?_, by linarith⟩
  rw [hbal]
  linarith

end TopEdge

end Graph

/-! ## Theorem 4.1.4: passing to the limit -/

section Limit

lemma mem_of_eventually_mem {Ks : ℕ → Set ℝ²} {L : Set ℝ²} (hLc : IsCompact L) (hLne : L.Nonempty)
    (hKc : ∀ i, IsCompact (Ks i)) (hKne : ∀ i, (Ks i).Nonempty)
    (hlim : Tendsto (fun i => Metric.hausdorffDist (Ks i) L) atTop (𝓝 0))
    {p : ℝ²} (hp : ∀ᶠ i in atTop, p ∈ Ks i) : p ∈ L := by
  have hinf : Metric.infDist p L ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [hp] with i hi
    exact Metric.infDist_le_hausdorffDist_of_mem hi
      (hausdorffEDist_ne_top_of_isCompact (hKc i) hLc (hKne i) hLne)
  exact (hLc.isClosed.mem_iff_infDist_zero hLne).2 (le_antisymm hinf Metric.infDist_nonneg)

lemma continuous_pt_sub (c : ℝ) : Continuous (fun y : ℝ => pt (c - y) 1) := by
  simp only [pt]
  exact ((continuous_const.sub continuous_id).smul continuous_const).add continuous_const

/-- A balanced maximum cap contains `o_ω`. -/
theorem IsBalancedMaxCap.oω_mem (hK : IsBalancedMaxCap K ω) : oω ω ∈ K := by
  obtain ⟨hcap, n, Ks, -, -, hmax, hlim⟩ := hK
  exact mem_of_eventually_mem hcap.isCompact hcap.nonempty (fun i => (hmax i).1.1.isCompact)
    (fun i => (hmax i).1.1.nonempty) hlim (Eventually.of_forall fun i => (hmax i).2.1)

/-- **Theorem 4.1.4.** A balanced maximum cap with `ω < π/2` contains the whole segment
`[o_ω − w°_K u₀, o_ω]`. -/
theorem IsBalancedMaxCap.mem_top_segment (hK : IsBalancedMaxCap K ω) (hω0 : 0 < ω)
    (hω1 : ω < π / 2) {g : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ gapWinf K ω) :
    pt ((1 - sin ω) / cos ω - g) 1 ∈ K := by
  have hoω : oω ω ∈ K := hK.oω_mem
  obtain ⟨hcap, n, Ks, -, hn, hmax, hlim⟩ := id hK
  have hP : ∀ i, PolySetup ω (uniformAngles ω (n i)) :=
    fun i => polySetup_uniform hω0 hω1.le (hn i).1
  have key : ∀ g' : ℝ, 0 ≤ g' → g' < gapWinf K ω → pt ((1 - sin ω) / cos ω - g') 1 ∈ K := by
    intro g' hg'0 hg'
    refine mem_of_eventually_mem hcap.isCompact hcap.nonempty (fun i => (hmax i).1.1.isCompact)
      (fun i => (hmax i).1.1.nonempty) hlim ?_
    have hswap : Tendsto (fun i => Metric.hausdorffDist K (Ks i)) atTop (𝓝 0) := by
      simpa [Metric.hausdorffDist_comm] using hlim
    have hc : Tendsto (fun i => (1 + (cos ω)⁻¹) * Metric.hausdorffDist K (Ks i)) atTop (𝓝 0) := by
      simpa using hswap.const_mul (1 + (cos ω)⁻¹)
    filter_upwards [hc.eventually (eventually_lt_nhds
      (by linarith : (0 : ℝ) < gapWinf K ω - g'))] with i hi
    have h1 := gapWinf_sub_le_gapWinf hcap (hmax i).1.1 hω0 hω1
    exact IsMaxPolyCap.mem_top_segment (hP i) hω1 (hmax i) hg'0 (by linarith)
  rcases lt_or_eq_of_le hg with hlt | heq
  · exact key g hg0 hlt
  rcases eq_or_lt_of_le hg0 with h0 | h0
  · rw [← h0, sub_zero]; exact hoω
  have h1 : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun m : ℕ => g - g * (1 / ((m : ℝ) + 1))) atTop (𝓝 g) := by
    simpa using tendsto_const_nhds.sub (h1.const_mul g)
  have htend : Tendsto (fun m : ℕ => pt ((1 - sin ω) / cos ω - (g - g * (1 / ((m : ℝ) + 1)))) 1)
      atTop (𝓝 (pt ((1 - sin ω) / cos ω - g) 1)) :=
    ((continuous_pt_sub ((1 - sin ω) / cos ω)).tendsto g).comp h2
  refine hcap.isCompact.isClosed.mem_of_tendsto htend ?_
  filter_upwards with m
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hmle : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 := by rw [div_le_one hm]; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ (m:ℝ))]
  have hmpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  refine key _ ?_ ?_
  · nlinarith
  · nlinarith

end Limit

end Sofa
