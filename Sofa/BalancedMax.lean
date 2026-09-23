/-
# Sofa/BalancedMax.lean — balanced maximum caps (Baek §3.5)

* uniform angle sets `Θ_{ω,2^k}` and their monotonicity;
* **Theorem 3.5.2**: a balanced maximum cap exists for every `ω ∈ (0, π/2]`;
* **Theorem 3.5.4**: `N(K_ω) ⊆ K_ω`;
* **Theorem 3.5.5**: `K_ω` maximizes the sofa area functional `A_ω`.

STATUS: in progress (2026-09-17, Opus 5).
-/
import Sofa.PolyMax

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {ω : ℝ}

/-! ## Uniform angle sets -/

lemma polySetup_uniform (hω0 : 0 < ω) (hω1 : ω ≤ π / 2) {n : ℕ} (hn : 1 < n) :
    PolySetup ω (uniformAngles ω n) := ⟨hω0, hω1, uniformAngles_isAngleSet hω0 hn⟩

lemma mem_uniformAngles {n i : ℕ} (hi0 : 0 < i) (hin : i < n) :
    (i : ℝ) * ω / n ∈ uniformAngles ω n :=
  Finset.mem_image.2 ⟨i, Finset.mem_Ioo.2 ⟨hi0, hin⟩, rfl⟩

lemma uniformAngles_mono {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hd : m ∣ n) :
    uniformAngles ω m ⊆ uniformAngles ω n := by
  intro t ht
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
  obtain ⟨hi0, him⟩ := Finset.mem_Ioo.1 hi
  obtain ⟨c, rfl⟩ := hd
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp at hn
    · exact hc
  have hlt : i * c < m * c := (Nat.mul_lt_mul_right hc).2 him
  have hval : ((i * c : ℕ) : ℝ) * ω / ((m * c : ℕ) : ℝ) = (i : ℝ) * ω / (m : ℝ) := by
    have hm' : (m : ℝ) ≠ 0 := by positivity
    have hc' : (c : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [← hval]
  exact mem_uniformAngles (by positivity) hlt

lemma half_mem_uniformAngles (hω0 : 0 < ω) (k : ℕ) :
    ω / 2 ∈ uniformAngles ω (2 ^ (k + 1)) := by
  have hpow : (0 : ℕ) < 2 ^ k := pow_pos (by norm_num) k
  have hval : ((2 ^ k : ℕ) : ℝ) * ω / ((2 ^ (k + 1) : ℕ) : ℝ) = ω / 2 := by
    push_cast
    rw [pow_succ]
    have : (2 : ℝ) ^ k ≠ 0 := by positivity
    field_simp
  rw [← hval]
  refine mem_uniformAngles hpow ?_
  rw [pow_succ]
  omega

/-! ## A lower bound for the area of the starting cap -/

section Square

variable {Θ : Finset ℝ} (hP : PolySetup ω Θ)
include hP

lemma quarter_le_areaH_one : (1 : ℝ) / 4 ≤ areaH ω Θ hP.nonempty (fun _ => 1) := by
  set h : ℝ → ℝ := fun _ => 1 with hh
  have hfloor : ∀ x, 0 ≤ x → floorF ω h x = 0 := by
    intro x hx
    refine le_antisymm ((Finset.sup'_le_iff _ _).2 fun s hs => ?_) ?_
    · have hsin := hP.sin_pos_fan hs
      have hcos : 0 ≤ cos s := by
        rcases mem_fanFin.1 hs with hs' | hs' <;> rw [hs']
        · exact cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos, hP.pos], hP.le⟩
        · rw [cos_pi_div_two]
      rw [hh, lineFn, sub_self, div_nonpos_iff]
      right
      exact ⟨by nlinarith, hsin.le⟩
    · refine le_trans (le_of_eq ?_)
        (Finset.le_sup' (fun s => lineFn s (h s - 1) x) (pi_div_two_mem_fanFin ω))
      rw [hh, lineFn, sub_self, cos_pi_div_two, sin_pi_div_two]
      ring
  have hroof : ∀ x, 0 ≤ x → x ≤ 1 / 2 → (1 : ℝ) / 2 ≤ roofU ω Θ h x := by
    intro x hx0 hx1
    rw [roofU, Finset.le_inf'_iff]
    intro s hs
    have hsin := hP.sin_pos hs
    have hcos : cos s ≤ 1 := cos_le_one s
    rw [hh, lineFn, le_div_iff₀ hsin]
    nlinarith [sin_le_one s, mul_le_mul_of_nonneg_left hcos hx0]
  have hR : ∀ x, roofR Θ hP.nonempty h x - floorF ω h x ≤
      roofU ω Θ h x - floorF ω h x ∨ True := fun _ => Or.inr trivial
  have hintU := integrable_posPart_U hP h
  have hintR := integrable_posPart_R hP h
  have hnR : ∀ x, max (roofR Θ hP.nonempty h x - floorF ω h x) 0 = 0 := by
    intro x
    have hempty := nicheH_one_eq_empty hP
    by_contra hne
    have hpos : 0 < roofR Θ hP.nonempty h x - floorF ω h x := by
      rcases lt_or_ge (roofR Θ hP.nonempty h x - floorF ω h x) 0 with hlt | hge
      · exact absurd (max_eq_right hlt.le) hne
      · rcases eq_or_lt_of_le hge with heq | hlt
        · exact absurd (max_eq_right (le_of_eq heq.symm)) hne
        · exact hlt
    have : pt x (floorF ω h x) ∈ nicheH ω Θ hP.nonempty h := by
      constructor
      · rw [pt_zero, pt_one]
      · rw [pt_zero, pt_one]; linarith
    rw [hempty] at this
    exact this
  have hlow : ∀ x ∈ Icc (0 : ℝ) (1 / 2), (1 : ℝ) / 2 ≤ max (roofU ω Θ h x - floorF ω h x) 0 := by
    rintro x ⟨hx0, hx1⟩
    refine le_trans ?_ (le_max_left _ _)
    rw [hfloor x hx0, sub_zero]
    exact hroof x hx0 hx1
  have h1 : (∫ _x in Icc (0:ℝ) (1/2), (1:ℝ)/2) ≤
      ∫ x in Icc (0:ℝ) (1/2), max (roofU ω Θ h x - floorF ω h x) 0 :=
    setIntegral_mono_on (integrableOn_const measure_Icc_lt_top.ne) hintU.integrableOn
      measurableSet_Icc hlow
  have h2 : (∫ x in Icc (0:ℝ) (1/2), max (roofU ω Θ h x - floorF ω h x) 0) ≤
      ∫ x, max (roofU ω Θ h x - floorF ω h x) 0 :=
    setIntegral_le_integral hintU (Eventually.of_forall fun x => le_max_right _ _)
  have hareaeq : areaH ω Θ hP.nonempty h = ∫ x, max (roofU ω Θ h x - floorF ω h x) 0 := by
    rw [areaH]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    rw [areaIntegrand, hnR x, sub_zero]
  rw [hareaeq]
  refine le_trans (le_of_eq ?_) (le_trans h1 h2)
  rw [setIntegral_const, Real.volume_real_Icc, max_eq_left (by norm_num : (0:ℝ) ≤ 1/2 - 0),
    smul_eq_mul]
  norm_num

lemma quarter_le_polySofaArea_one :
    (1 : ℝ) / 4 ≤ polySofaArea ω Θ (capH ω Θ (fun _ => 1)) := by
  have hK₁ : IsPolyCap ω Θ (capH ω Θ (fun _ => 1)) := isPolyCap_one hP
  refine le_trans (quarter_le_areaH_one hP) ?_
  rw [polySofaArea_eq_areaH hP hK₁.1]
  exact areaH_le_areaH_supportFn hP rfl rfl hK₁

end Square

/-! ## Hausdorff limits of caps -/

section Limit

/-- Upper semicontinuity of the volume along Hausdorff convergence. -/
lemma le_volume_of_tendsto_hausdorffDist {Ks : ℕ → Set ℝ²} {L : Set ℝ²}
    (hKc : ∀ i, IsCompact (Ks i)) (hKne : ∀ i, (Ks i).Nonempty)
    (hLc : IsCompact L) (hLne : L.Nonempty)
    (htend : Tendsto (fun i => Metric.hausdorffDist (Ks i) L) atTop (𝓝 0))
    {c : ENNReal} (hc : ∃ᶠ i in atTop, c ≤ volume (Ks i)) : c ≤ volume L := by
  have hsub : ∀ δ : ℝ, 0 < δ → ∀ᶠ i in atTop, Ks i ⊆ Metric.cthickening δ L := by
    intro δ hδ
    filter_upwards [htend.eventually (eventually_lt_nhds hδ)] with i hi
    intro x hx
    obtain ⟨y, hy, hdy⟩ := hLc.exists_infDist_eq_dist hLne x
    refine Metric.mem_cthickening_of_dist_le x y δ L hy ?_
    rw [← hdy]
    exact le_trans (Metric.infDist_le_hausdorffDist_of_mem hx
      (hausdorffEDist_ne_top_of_isCompact (hKc i) hLc (hKne i) hLne)) hi.le
  have hle : ∀ δ : ℝ, 0 < δ → c ≤ volume (Metric.cthickening δ L) := by
    intro δ hδ
    obtain ⟨i, hi1, hi2⟩ := ((hsub δ hδ).and_frequently hc).exists
    exact le_trans hi2 (measure_mono hi1)
  have hlim : Tendsto (fun δ : ℝ => volume (Metric.cthickening δ L)) (𝓝[>] (0 : ℝ))
      (𝓝 (volume L)) :=
    (tendsto_measure_cthickening_of_isCompact hLc).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hle δ hδ

/-- Upper semicontinuity of the volume, in the `ε`-form. -/
lemma eventually_volume_le_of_tendsto_hausdorffDist {Ks : ℕ → Set ℝ²} {L : Set ℝ²}
    (hKc : ∀ i, IsCompact (Ks i)) (hKne : ∀ i, (Ks i).Nonempty)
    (hLc : IsCompact L) (hLne : L.Nonempty)
    (htend : Tendsto (fun i => Metric.hausdorffDist (Ks i) L) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, (volume (Ks i)).toReal ≤ (volume L).toReal + ε := by
  have hLtop : volume L ≠ ⊤ := hLc.measure_lt_top.ne
  by_contra hcon
  rw [not_eventually] at hcon
  have hfr : ∃ᶠ i in atTop, ENNReal.ofReal ((volume L).toReal + ε) ≤ volume (Ks i) := by
    refine hcon.mono fun i hi => ?_
    rw [not_le] at hi
    exact le_trans (ENNReal.ofReal_le_ofReal hi.le)
      (le_of_eq (ENNReal.ofReal_toReal (hKc i).measure_lt_top.ne))
  have hkey := le_volume_of_tendsto_hausdorffDist hKc hKne hLc hLne htend hfr
  rw [ENNReal.ofReal_le_iff_le_toReal hLtop] at hkey
  linarith

/-- A Fatou-type lower bound: if every point of `N` eventually lies in `Ns i`, the volumes of
`Ns i` are eventually almost as large as the volume of `N`. -/
lemma eventually_le_volume_of_eventually_mem {Ns : ℕ → Set ℝ²} {N : Set ℝ²}
    (hNfin : volume N ≠ ⊤) (hNsfin : ∀ i, volume (Ns i) ≠ ⊤)
    (hmem : ∀ p ∈ N, ∀ᶠ i in atTop, p ∈ Ns i) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, (volume N).toReal - ε ≤ (volume (Ns i)).toReal := by
  rcases le_or_gt ((volume N).toReal - ε) 0 with hneg | hpos
  · exact Eventually.of_forall fun i => le_trans hneg ENNReal.toReal_nonneg
  set A : ℕ → Set ℝ² := fun m => ⋂ i, ⋂ (_ : m ≤ i), Ns i with hA
  have hAmono : Monotone A := by
    intro a b hab
    exact iInter₂_mono' fun i hi => ⟨i, le_trans hab hi, le_rfl⟩
  have hNsub : N ⊆ ⋃ m, A m := by
    intro p hp
    obtain ⟨m, hm⟩ := eventually_atTop.1 (hmem p hp)
    exact mem_iUnion.2 ⟨m, mem_iInter₂.2 fun i hi => hm i hi⟩
  have htend : Tendsto (fun m => volume (A m)) atTop (𝓝 (volume (⋃ m, A m))) :=
    tendsto_measure_iUnion_atTop hAmono
  have hlt : ENNReal.ofReal ((volume N).toReal - ε) < volume (⋃ m, A m) := by
    refine lt_of_lt_of_le ?_ (measure_mono hNsub)
    rw [ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hNfin]
    linarith
  obtain ⟨m, hm⟩ := ((tendsto_order.1 htend).1 _ hlt).exists
  filter_upwards [eventually_ge_atTop m] with i hi
  rw [← ENNReal.ofReal_le_iff_le_toReal (hNsfin i)]
  exact le_trans hm.le (measure_mono (fun q hq => mem_iInter₂.1 hq i hi))

/-- A Hausdorff limit of caps with positive volume is a cap. -/
theorem isCap_of_tendsto {Ks : ℕ → Set ℝ²} {L : Set ℝ²}
    (hKcap : ∀ i, IsCap (Ks i) ω) (hLc : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hLvol : volume L ≠ 0)
    (htend : Tendsto (fun i => Metric.hausdorffDist (Ks i) L) atTop (𝓝 0)) : IsCap L ω := by
  have hconv : ∀ s : ℝ, Tendsto (fun i => supportFn (Ks i) s) atTop (𝓝 (supportFn L s)) := by
    intro s
    have hb : ∀ i, |supportFn (Ks i) s - supportFn L s| ≤ Metric.hausdorffDist (Ks i) L :=
      fun i => abs_supportFn_sub_le_hausdorffDist (hKcap i).isCompact hLc
        (hKcap i).nonempty hLne s
    have := squeeze_zero_norm' (Eventually.of_forall fun i => by
      rw [Real.norm_eq_abs]; exact hb i) htend
    exact tendsto_sub_nhds_zero_iff.1 this
  have hval : ∀ (s c : ℝ), (∀ i, supportFn (Ks i) s = c) → supportFn L s = c := by
    intro s c hs
    have hts := hconv s
    simp only [hs] at hts
    exact tendsto_nhds_unique hts tendsto_const_nhds
  -- an interior point of `L`
  have hint : (interior L).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hspan : affineSpan ℝ L ≠ ⊤ := by
      intro hh
      rw [← Set.not_nonempty_iff_eq_empty] at hemp
      exact hemp (hLconv.interior_nonempty_iff_affineSpan_eq_top.2 hh)
    exact hLvol (measure_mono_null (subset_affineSpan ℝ L)
      (Measure.addHaar_affineSubspace volume _ hspan))
  obtain ⟨q, hq⟩ := hint
  obtain ⟨δ, hδ0, hball⟩ := Metric.isOpen_iff.1 isOpen_interior q hq
  have hmargin : ∀ s : ℝ, ⟪q, u s⟫ + δ / 2 ≤ supportFn L s := by
    intro s
    have hmem : q + (δ / 2) • u s ∈ L := by
      refine interior_subset (hball ?_)
      rw [Metric.mem_ball, dist_eq_norm, show q + (δ / 2) • u s - q = (δ / 2) • u s by abel,
        norm_smul, norm_u, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    have hle := le_supportFn hLc hmem s
    rw [inner_add_left, real_inner_smul_left, inner_u_u_eq_cos, sub_self, cos_zero,
      mul_one] at hle
    linarith
  refine ⟨hLconv, hLc, hLne, hval _ _ fun i => (hKcap i).supportFn_ω,
    hval _ _ fun i => (hKcap i).supportFn_pi_div_two,
    hval _ _ fun i => (hKcap i).supportFn_ω_add_pi,
    hval _ _ fun i => (hKcap i).supportFn_three_pi_div_two, ?_⟩
  refine subset_antisymm (fun p hp => mem_iInter₂.2 fun s _ => le_supportFn hLc hp s) ?_
  intro p hp
  rw [mem_iInter₂] at hp
  simp only [hpLe, mem_ofPred_eq] at hp
  -- the points `p_λ` on the segment towards `q`
  set pl : ℕ → ℝ² := fun m => (1 - 1 / ((m : ℝ) + 1)) • p + (1 / ((m : ℝ) + 1)) • q with hpldef
  have hmem : ∀ m : ℕ, pl m ∈ L := by
    intro m
    set l : ℝ := 1 / ((m : ℝ) + 1) with hl
    have hl0 : 0 < l := by positivity
    have hl1 : l ≤ 1 := by
      rw [hl, div_le_one (by positivity)]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hmarg : ∀ s ∈ capAngles ω, ⟪pl m, u s⟫ ≤ supportFn L s - l * (δ / 2) := by
      intro s hs
      have h1 := hp s hs
      have h2 := hmargin s
      rw [hpldef]
      simp only [inner_add_left, real_inner_smul_left]
      nlinarith [hl0, hl1]
    have hmemi : ∀ᶠ i in atTop, pl m ∈ Ks i := by
      filter_upwards [htend.eventually (eventually_lt_nhds
        (by positivity : (0:ℝ) < l * (δ / 2)))] with i hi
      rw [(hKcap i).mem_iff]
      intro s hs
      have h1 : |supportFn (Ks i) s - supportFn L s| ≤ Metric.hausdorffDist (Ks i) L :=
        abs_supportFn_sub_le_hausdorffDist (hKcap i).isCompact hLc (hKcap i).nonempty hLne s
      have h2 := hmarg s hs
      have h3 := abs_le.1 h1
      linarith [h3.1, h3.2]
    have hinf : Metric.infDist (pl m) L ≤ 0 := by
      refine ge_of_tendsto htend ?_
      filter_upwards [hmemi] with i hi
      exact Metric.infDist_le_hausdorffDist_of_mem hi
        (hausdorffEDist_ne_top_of_isCompact (hKcap i).isCompact hLc (hKcap i).nonempty hLne)
    have : Metric.infDist (pl m) L = 0 := le_antisymm hinf Metric.infDist_nonneg
    exact (hLc.isClosed.mem_iff_infDist_zero hLne).2 this
  have htendp : Tendsto pl atTop (𝓝 p) := by
    have h1 : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := ((tendsto_const_nhds (x := (1 : ℝ))).sub h1).smul (tendsto_const_nhds (x := p))
    have h3 := h1.smul (tendsto_const_nhds (x := q))
    have h4 := h2.add h3
    rw [hpldef]
    simpa using h4
  exact hLc.isClosed.mem_of_tendsto htendp (Eventually.of_forall hmem)

end Limit

/-! ## Density of the uniform angle sets -/

section Mesh

lemma exists_mem_uniformAngles (hω0 : 0 < ω) {t : ℝ} (ht0 : 0 < t) (_htω : t < ω)
    {ε : ℝ} (_hε : 0 < ε) {m : ℕ} (hm0 : 0 < m) (hmε : ω / m < ε) (hmt : ω / m < ω - t) :
    ∃ t' ∈ uniformAngles ω m, t < t' ∧ t' - t < ε := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
  have hx0 : 0 ≤ t * m / ω := by positivity
  have hjle : ((⌊t * m / ω⌋₊ : ℕ) : ℝ) ≤ t * m / ω := Nat.floor_le hx0
  have hjlt : t * m / ω < (⌊t * m / ω⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one _
  set j : ℕ := ⌊t * m / ω⌋₊ with hj
  have hjle' : (j : ℝ) * ω ≤ t * m := by rwa [le_div_iff₀ hω0] at hjle
  have hjlt' : t * m < ((j : ℝ) + 1) * ω := by rwa [div_lt_iff₀ hω0] at hjlt
  have hjm : j + 1 < m := by
    have h1 : ω < (ω - t) * m := (div_lt_iff₀ hm').1 hmt
    have h3 : ((j : ℝ) + 1) * ω < (m : ℝ) * ω := by nlinarith
    have h2 : ((j : ℝ) + 1) < m := lt_of_mul_lt_mul_right h3 hω0.le
    exact_mod_cast h2
  have e1 : t < ((j : ℝ) + 1) * ω / m := by rw [lt_div_iff₀ hm']; linarith
  have e2 : ((j : ℝ) + 1) * ω / m - t < ε := by
    have hA : ((j : ℝ) + 1) * ω / m = (j : ℝ) * ω / m + ω / m := by ring
    have hB : (j : ℝ) * ω / m ≤ t := by rw [div_le_iff₀ hm']; linarith
    rw [hA]; linarith
  refine ⟨_, mem_uniformAngles (n := m) (i := j + 1) (Nat.succ_pos j) hjm, ?_, ?_⟩
  · push_cast; exact e1
  · push_cast; exact e2

lemma eventually_exists_mem_uniformAngles (hω0 : 0 < ω) {t : ℝ} (ht0 : 0 < t) (htω : t < ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∃ t' ∈ uniformAngles ω m, t < t' ∧ t' - t < ε := by
  have hlim : Tendsto (fun m : ℕ => ω / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat ω
  filter_upwards [eventually_gt_atTop 0, hlim.eventually (eventually_lt_nhds hε),
    hlim.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < ω - t))] with m hm0 h1 h2
  exact exists_mem_uniformAngles hω0 ht0 htω hε hm0 h1 h2

/-- Every point of the niche of the limit cap eventually lies in the polygon niches. -/
theorem eventually_mem_polyNiche {K : Set ℝ²} {Ks : ℕ → Set ℝ²} {ns : ℕ → ℕ}
    (hω0 : 0 < ω) (hKc : IsCompact K) (hKne : K.Nonempty)
    (hKsc : ∀ i, IsCompact (Ks i)) (hKsne : ∀ i, (Ks i).Nonempty)
    (hns : Tendsto ns atTop atTop)
    (hlim : Tendsto (fun i => Metric.hausdorffDist (Ks i) K) atTop (𝓝 0))
    {p : ℝ²} (hp : p ∈ niche K ω) :
    ∀ᶠ i in atTop, p ∈ polyNiche ω (uniformAngles ω (ns i)) (Ks i) := by
  obtain ⟨hfan, t, ht, hQ⟩ := mem_niche_iff.1 hp
  rw [mem_QminusS_iff] at hQ
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hKc.isBounded
  obtain ⟨q₀, hq₀⟩ := hKne
  have hR0 : 0 ≤ R := le_trans (norm_nonneg q₀) (hR q₀ hq₀)
  set g : ℝ := min (supportFn K t - 1 - ⟪p, u t⟫)
      (supportFn K (t + π / 2) - 1 - ⟪p, u (t + π / 2)⟫) with hg
  have hg0 : 0 < g := lt_min (by linarith [hQ.1]) (by linarith [hQ.2])
  set C : ℝ := ‖p‖ + R + 1 with hC
  have hC0 : 0 < C := by rw [hC]; positivity
  set ε : ℝ := g / (2 * C) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  filter_upwards [hns.eventually (eventually_exists_mem_uniformAngles hω0 ht.1 ht.2 hε0),
    hlim.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < g / 2))] with i hi hd
  obtain ⟨t', ht'mem, ht'gt, ht'lt⟩ := hi
  have step : ∀ s : ℝ, g ≤ supportFn K s - 1 - ⟪p, u s⟫ →
      ⟪p, u (s + (t' - t))⟫ < supportFn (Ks i) (s + (t' - t)) - 1 := by
    intro s hs
    have hdiff : |s + (t' - t) - s| = t' - t := by
      rw [show s + (t' - t) - s = t' - t by ring, abs_of_pos (by linarith)]
    have h1 : |⟪p, u (s + (t' - t))⟫ - ⟪p, u s⟫| ≤ ‖p‖ * |s + (t' - t) - s| := by
      have e : ⟪p, u (s + (t' - t))⟫ - ⟪p, u s⟫ = ⟪p, u (s + (t' - t)) - u s⟫ := by
        rw [inner_sub_right]
      rw [e]
      calc |⟪p, u (s + (t' - t)) - u s⟫| ≤ ‖p‖ * ‖u (s + (t' - t)) - u s‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ ‖p‖ * |s + (t' - t) - s| :=
            mul_le_mul_of_nonneg_left (norm_u_sub_u_le _ _) (norm_nonneg p)
    have h2 : |supportFn K (s + (t' - t)) - supportFn K s| ≤ R * |s + (t' - t) - s| :=
      abs_supportFn_sub_le hKc ⟨q₀, hq₀⟩ hR _ _
    have h3 : |supportFn (Ks i) (s + (t' - t)) - supportFn K (s + (t' - t))| ≤
        Metric.hausdorffDist (Ks i) K :=
      abs_supportFn_sub_le_hausdorffDist (hKsc i) hKc (hKsne i) ⟨q₀, hq₀⟩ _
    rw [hdiff] at h1 h2
    have hkey : (‖p‖ + R) * (t' - t) ≤ g / 2 := by
      have h4 : (‖p‖ + R) * (t' - t) ≤ C * ε :=
        mul_le_mul (by rw [hC]; linarith) ht'lt.le (by linarith) hC0.le
      have h5 : C * ε = g / 2 := by rw [hε]; field_simp
      linarith
    have a1 := abs_le.1 h1
    have a2 := abs_le.1 h2
    have a3 := abs_le.1 h3
    nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
  refine ⟨hfan, mem_iUnion₂.2 ⟨t', ht'mem, ?_⟩⟩
  rw [mem_QminusS_iff]
  constructor
  · have hst := step t (by rw [hg]; exact min_le_left _ _)
    rwa [show t + (t' - t) = t' by ring] at hst
  · have hst := step (t + π / 2) (by rw [hg]; exact min_le_right _ _)
    rwa [show t + π / 2 + (t' - t) = t' + π / 2 by ring] at hst

end Mesh

/-! ## Theorem 3.5.2: existence of balanced maximum caps -/

section Existence

/-- A polygon cap equals its own polygon cap hull, so its volume dominates `A_Θ`. -/
lemma polySofaArea_le_volume {Θ : Finset ℝ} (hP : PolySetup ω Θ) {K : Set ℝ²}
    (hK : IsPolyCap ω Θ K) : polySofaArea ω Θ K ≤ (volume K).toReal := by
  have hPC : polyCap ω Θ K = K := by
    rw [polyCap_eq_capH hP hK.1, capH_supportFn hP hK]
  simp only [polySofaArea, hPC]
  have : 0 ≤ (volume (polyNiche ω Θ K)).toReal := ENNReal.toReal_nonneg
  linarith

lemma ofReal_le_volume_of_polySofaArea {Θ : Finset ℝ} (hP : PolySetup ω Θ) {K : Set ℝ²}
    (hK : IsPolyCap ω Θ K) {c : ℝ} (hc : c ≤ polySofaArea ω Θ K) :
    ENNReal.ofReal c ≤ volume K := by
  rw [ENNReal.ofReal_le_iff_le_toReal hK.1.isCompact.measure_lt_top.ne]
  exact hc.trans (polySofaArea_le_volume hP hK)

/-- **Theorem 3.5.2.** For every rotation angle `ω ∈ (0, π/2]` a balanced maximum cap exists. -/
theorem exists_isBalancedMaxCap (hω0 : 0 < ω) (hω1 : ω ≤ π / 2) :
    ∃ K, IsBalancedMaxCap K ω := by
  classical
  have hn1 : ∀ i : ℕ, 1 < 2 ^ (i + 1) := by
    intro i
    calc (1 : ℕ) < 2 := one_lt_two
      _ = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hP : ∀ i : ℕ, PolySetup ω (uniformAngles ω (2 ^ (i + 1))) :=
    fun i => polySetup_uniform hω0 hω1 (hn1 i)
  choose Ks hKs using fun i : ℕ => exists_isMaxPolyCap (hP i)
  have harea : ∀ i, (1 : ℝ) / 4 ≤ polySofaArea ω (uniformAngles ω (2 ^ (i + 1))) (Ks i) :=
    fun i => le_trans (quarter_le_polySofaArea_one (hP i))
      ((hKs i).2.2 _ (isPolyCap_one (hP i)))
  obtain ⟨R, hR0, hRball⟩ :=
    exists_ball hω0 hω1 (by positivity : (0 : ℝ) < ω / 2) (by linarith : ω / 2 < ω)
  have hball : ∀ i, Ks i ⊆ Metric.closedBall (0 : ℝ²) R := fun i =>
    hRball _ (hP i) (half_mem_uniformAngles hω0 i) _ (hKs i).1 (hKs i).2.1
      (le_trans (by norm_num) (harea i))
  obtain ⟨L, φ, hφ, hLc, hLne, hLconv, -, hlim⟩ :=
    exists_tendsto_hausdorffDist (fun i => (hKs i).1.1.isCompact)
      (fun i => (hKs i).1.1.nonempty) (fun i => (hKs i).1.1.convex) hball
  have hvol : ENNReal.ofReal ((1 : ℝ) / 4) ≤ volume L :=
    le_volume_of_tendsto_hausdorffDist (fun i => (hKs (φ i)).1.1.isCompact)
      (fun i => (hKs (φ i)).1.1.nonempty) hLc hLne hlim
      (Eventually.of_forall
        (fun i => ofReal_le_volume_of_polySofaArea (hP (φ i)) (hKs (φ i)).1 (harea (φ i)))).frequently
  have hLvol : volume L ≠ 0 := by
    intro h0
    rw [h0, le_zero_iff, ENNReal.ofReal_eq_zero] at hvol
    norm_num at hvol
  refine ⟨L, isCap_of_tendsto (fun i => (hKs (φ i)).1.1) hLc hLne hLconv hLvol hlim,
    fun i => 2 ^ (φ i + 1), fun i => Ks (φ i), ?_, fun i => ⟨hn1 (φ i), φ i + 1, rfl⟩,
    fun i => hKs (φ i), hlim⟩
  intro i j hij
  exact Nat.pow_lt_pow_right one_lt_two (by have := hφ hij; omega)

end Existence

/-! ## Theorem 3.5.4: a balanced maximum cap contains its niche -/

section Niche

variable {K : Set ℝ²}

/-- **Theorem 3.5.4.** A balanced maximum cap contains its niche. -/
theorem IsBalancedMaxCap.niche_subset (hK : IsBalancedMaxCap K ω) (hω0 : 0 < ω)
    (hω1 : ω ≤ π / 2) : niche K ω ⊆ K := by
  obtain ⟨hcap, n, Ks, hmono, hn, hmax, hlim⟩ := hK
  have hP : ∀ i, PolySetup ω (uniformAngles ω (n i)) :=
    fun i => polySetup_uniform hω0 hω1 (hn i).1
  have hsub : ∀ i, polyNiche ω (uniformAngles ω (n i)) (Ks i) ⊆ Ks i := fun i =>
    polyNiche_subset_of_balanced (hP i) (hmax i).1
      (fun s hs => IsMaxPolyCap.balanced (hP i) (hmax i) hs)
  intro p hp
  have hev := eventually_mem_polyNiche hω0 hcap.isCompact hcap.nonempty
    (fun i => (hmax i).1.1.isCompact) (fun i => (hmax i).1.1.nonempty)
    hmono.tendsto_atTop hlim hp
  have hinf : Metric.infDist p K ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [hev] with i hi
    exact Metric.infDist_le_hausdorffDist_of_mem (hsub i hi)
      (hausdorffEDist_ne_top_of_isCompact (hmax i).1.1.isCompact hcap.isCompact
        (hmax i).1.1.nonempty hcap.nonempty)
  exact (hcap.isCompact.isClosed.mem_iff_infDist_zero hcap.nonempty).2
    (le_antisymm hinf Metric.infDist_nonneg)

end Niche

/-! ## Theorem 3.5.5: a balanced maximum cap maximizes `A_ω` -/

section Max

variable {Θ : Finset ℝ} {K : Set ℝ²}

lemma polyCap_congr {A B : Set ℝ²}
    (h : ∀ s ∈ diamondFin ω Θ, supportFn A s = supportFn B s) :
    polyCap ω Θ A = polyCap ω Θ B := by
  rw [polyCap, polyCap]
  congr 1
  exact iInter₂_congr fun t ht =>
    QplusS_congr (h t (mem_diamondFin_of_mem ht)) (h _ (add_mem_diamondFin ht))

lemma polyNiche_congr {A B : Set ℝ²}
    (h : ∀ s ∈ diamondFin ω Θ, supportFn A s = supportFn B s) :
    polyNiche ω Θ A = polyNiche ω Θ B := by
  rw [polyNiche, polyNiche]
  congr 1
  exact iUnion₂_congr fun t ht =>
    QminusS_congr (h t (mem_diamondFin_of_mem ht)) (h _ (add_mem_diamondFin ht))

lemma polySofaArea_congr {A B : Set ℝ²}
    (h : ∀ s ∈ diamondFin ω Θ, supportFn A s = supportFn B s) :
    polySofaArea ω Θ A = polySofaArea ω Θ B := by
  rw [polySofaArea, polySofaArea, polyCap_congr h, polyNiche_congr h]

lemma isCompact_polyCap (hP : PolySetup ω Θ) (hK : IsCap K ω) :
    IsCompact (polyCap ω Θ K) := by
  rw [polyCap_eq_capH hP hK]; exact isCompact_capH hP _

lemma nonempty_polyCap (hK : IsCap K ω) : (polyCap ω Θ K).Nonempty :=
  hK.nonempty.mono (subset_polyCap hK Θ)

lemma supportFn_polyCap (hP : PolySetup ω Θ) (hK : IsCap K ω) {s : ℝ}
    (hs : s ∈ diamondFin ω Θ) : supportFn (polyCap ω Θ K) s = supportFn K s := by
  refine le_antisymm ?_ (supportFn_mono (isCompact_polyCap hP hK) hK.nonempty
    (subset_polyCap hK Θ) s)
  have hne : (capH ω Θ (supportFn K)).Nonempty := by
    rw [← polyCap_eq_capH hP hK]; exact nonempty_polyCap hK
  rw [polyCap_eq_capH hP hK]
  exact supportFn_capH_le hP _ hs hne

/-- The polygon cap hull of a cap is a polygon cap. -/
lemma isPolyCap_polyCap (hP : PolySetup ω Θ) (hK : IsCap K ω) :
    IsPolyCap ω Θ (polyCap ω Θ K) := by
  have hsub : K ⊆ capH ω Θ (supportFn K) := by
    rw [← polyCap_eq_capH hP hK]; exact subset_polyCap hK Θ
  rw [polyCap_eq_capH hP hK]
  refine isPolyCap_capH hP hK.supportFn_ω hK.supportFn_pi_div_two ?_ ?_
  · intro s _
    obtain ⟨q, hq, hval⟩ := exists_supportFn_eq hK.isCompact hK.nonempty s
    exact ⟨q, hsub hq, hval⟩
  · intro s hs
    have hsval : supportFn K s = 1 := by
      rcases mem_fanFin.1 hs with h | h
      · rw [h]; exact hK.supportFn_ω
      · rw [h]; exact hK.supportFn_pi_div_two
    have hzero : supportFn K (s + π) = 0 := by
      rcases mem_fanFin.1 hs with h | h
      · rw [h]; exact hK.supportFn_ω_add_pi
      · rw [h, show π / 2 + π = 3 * π / 2 by ring]; exact hK.supportFn_three_pi_div_two
    obtain ⟨q, hq, hval⟩ := exists_supportFn_eq hK.isCompact hK.nonempty (s + π)
    refine ⟨q, hsub hq, ?_⟩
    rw [u_add_pi, inner_neg_right, hzero] at hval
    rw [hsval]
    linarith

/-- **Theorem 3.5.5.** A balanced maximum cap maximizes the sofa area functional `A_ω`. -/
theorem IsBalancedMaxCap.isMax (hK : IsBalancedMaxCap K ω) (hω0 : 0 < ω) (hω1 : ω ≤ π / 2)
    {K' : Set ℝ²} (hK' : IsCap K' ω) : sofaArea K' ω ≤ sofaArea K ω := by
  obtain ⟨hcap, n, Ks, hmono, hn, hmax, hlim⟩ := hK
  have hP : ∀ i, PolySetup ω (uniformAngles ω (n i)) :=
    fun i => polySetup_uniform hω0 hω1 (hn i).1
  have hKsc : ∀ i, IsCap (Ks i) ω := fun i => (hmax i).1.1
  -- every polygon cap functional dominates `A_ω(K')`
  have hlow : ∀ i, sofaArea K' ω ≤ polySofaArea ω (uniformAngles ω (n i)) (Ks i) := by
    intro i
    refine le_trans (hK'.sofaArea_le_polySofaArea hω0 hω1 (hP i).angles) ?_
    have heq : polySofaArea ω (uniformAngles ω (n i))
        (polyCap ω (uniformAngles ω (n i)) K') = polySofaArea ω (uniformAngles ω (n i)) K' :=
      polySofaArea_congr fun s hs => supportFn_polyCap (hP i) hK' hs
    rw [← heq]
    exact (hmax i).2.2 _ (isPolyCap_polyCap (hP i) hK')
  -- the polygon cap of a maximum polygon cap is itself
  have hself : ∀ i, polyCap ω (uniformAngles ω (n i)) (Ks i) = Ks i := fun i => by
    rw [polyCap_eq_capH (hP i) (hKsc i), capH_supportFn (hP i) (hmax i).1]
  -- finiteness
  have hNfin : volume (niche K ω) ≠ ⊤ :=
    (hcap.isBounded_niche hω0 hω1).measure_lt_top.ne
  have hNsfin : ∀ i, volume (polyNiche ω (uniformAngles ω (n i)) (Ks i)) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top ((hKsc i).isBounded_niche hω0 hω1).measure_lt_top.ne
      (measure_mono (polyNiche_subset_niche (hP i).angles (Ks i)))
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hU := eventually_volume_le_of_tendsto_hausdorffDist (fun i => (hKsc i).isCompact)
    (fun i => (hKsc i).nonempty) hcap.isCompact hcap.nonempty hlim (half_pos hε)
  have hN := eventually_le_volume_of_eventually_mem (Ns := fun i =>
      polyNiche ω (uniformAngles ω (n i)) (Ks i)) hNfin hNsfin
    (fun p hp => eventually_mem_polyNiche hω0 hcap.isCompact hcap.nonempty
      (fun i => (hKsc i).isCompact) (fun i => (hKsc i).nonempty) hmono.tendsto_atTop hlim hp)
    (half_pos hε)
  obtain ⟨i, hi1, hi2⟩ := (hU.and hN).exists
  have hkey := hlow i
  rw [polySofaArea, hself i] at hkey
  have hgoal : sofaArea K ω = (volume K).toReal - (volume (niche K ω)).toReal := rfl
  rw [hgoal]
  linarith

end Max

end Sofa
