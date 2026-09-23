/-
# Sofa/EndPoint.lean — closing the endpoint-angle gap, and `f_K(0) = 1`

Baek's Lemma 6.5.2 uses `f_K(0) = 1`, justified only in the informal sketch §1.7.3 ("because the
point `A(0)` should be on the x-axis").  Rigorously it splits in two:

* `e^{min}_K(0) = 0` for **every** cap with `ω = π/2` (`edgeMin_zero_of_isCap`): the point
  `(h_K(0), 0)` lies in `K`, because `⟪(h_K(0),0), u_r⟫ ≤ ⟪v⁺_K(0), u_r⟫` for every normal angle
  `r` with `sin r ≥ 0`, and `capAngles (π/2) = [0, π] ∪ {3π/2}`;
* `σ_K({0}) = |e_K(0)| = 0`, which is Theorem 6.4.3 on `I = [0, b)`.  Its proof needs Theorem
  6.3.3 at the endpoint angle `t = δ`, where `t − δ = 0 ∉ Θ` — the gap of `blueprint §19.4`.

This file closes that gap with a *different* bound, which needs no neighbouring angles at all.
For a maximum polygon cap the balanced condition (Thm 3.4.9) gives `σ(t) = τ(t)`, and the niche
side at normal `t` is trapped between the fan floor `y = 0` and the inner wall `d_t`, so

    `τ(t) ≤ ((h(t) − 1)·tan t + (h(t + π/2) − 1))⁺`      (`tauH_le_crude`)

for **every** `t ∈ Θ`.  At `t = δ` the right-hand side is `O(δ)` because `h(π/2) = 1` and `h` is
Lipschitz — which is exactly what the `t = δ` term of Equation (6.5) needs.

STATUS: [PROOF-C-local] round 1 (2026-09-22, Opus 5).
-/
import Sofa.PolyGap

noncomputable section

open Real Set Filter Topology MeasureTheory Metric
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²}

/-! ## `e^{min}_K(0) = 0` for every cap -/

lemma inner_v_zero_nonneg (hK : IsCap K (π / 2)) {p : ℝ²} (hp : p ∈ K) : 0 ≤ ⟪p, v 0⟫ := by
  have h := hK.inner_le hp (3 * π / 2)
  rw [hK.supportFn_three_pi_div_two, u_three_pi_div_two, inner_neg_right,
    ← v_zero_eq] at h
  linarith

/-- **`e^{min}_K(0) = 0`**: the `x`-maximal face of a cap reaches the floor `y = 0`. -/
theorem edgeMin_zero_of_isCap (hK : IsCap K (π / 2)) : edgeMin K 0 = 0 := by
  have hKc := hK.isCompact
  have hKne := hK.nonempty
  have hPmem : vtxP K 0 ∈ K := vtxP_mem hKc hKne 0
  have he0 : 0 ≤ edgeMax K 0 := by
    rw [← inner_vtxP_v]; exact inner_v_zero_nonneg hK hPmem
  -- the point `Q = h_K(0) • u_0 = (h_K(0), 0)`
  set Q : ℝ² := supportFn K 0 • u 0 with hQdef
  have hQu : ∀ r : ℝ, ⟪Q, u r⟫ = supportFn K 0 * cos r := by
    intro r
    rw [hQdef, real_inner_smul_left, inner_u_u_eq_cos, zero_sub, cos_neg]
  have hPu : ∀ r : ℝ, ⟪vtxP K 0, u r⟫ = supportFn K 0 * cos r + edgeMax K 0 * sin r := by
    intro r
    rw [u_frame 0 r, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      inner_vtxP_u, inner_vtxP_v, sub_zero]
    ring
  have hQmem : Q ∈ K := by
    rw [hK.eq_iInter]
    refine mem_iInter₂.2 fun r hr => ?_
    have hsin : 0 ≤ sin r ∨ r = 3 * π / 2 := by
      rcases hr with (hr | hr) | hr
      · exact Or.inl (sin_nonneg_of_nonneg_of_le_pi hr.1 (by linarith [hr.2, pi_pos]))
      · exact Or.inl
          (sin_nonneg_of_nonneg_of_le_pi (by linarith [hr.1, pi_pos]) (by linarith [hr.2]))
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
        rcases hr with hr | hr
        · exact Or.inr (by rw [hr]; ring)
        · exact Or.inr hr
    simp only [hpLe, mem_ofPred_eq]
    rcases hsin with hs | hs
    · have h1 := hK.inner_le hPmem r
      rw [hPu r] at h1
      rw [hQu r]
      nlinarith [mul_nonneg he0 hs]
    · subst hs
      rw [hQu, hK.supportFn_three_pi_div_two, show cos (3 * π / 2) = 0 from by
        rw [show (3 : ℝ) * π / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two, neg_zero],
        mul_zero]
  have hQedge : Q ∈ edge K 0 := by
    refine ⟨hQmem, ?_⟩
    simp only [supportLine, line, mem_ofPred_eq]
    rw [hQu, cos_zero, mul_one]
  have hle : edgeMin K 0 ≤ 0 := by
    have := edgeMin_le_inner_v hKc hQedge
    rwa [hQdef, real_inner_smul_left, inner_u_v, mul_zero] at this
  have hge : 0 ≤ edgeMin K 0 := by
    rw [← inner_vtxM_v]; exact inner_v_zero_nonneg hK (vtxM_mem hKc hKne 0)
  linarith

/-- Hence `f⁻_K(0) = 1` for every cap with `ω = π/2`, and `f⁺_K(0) = 1 − σ_K({0})`. -/
theorem armFm_zero_of_isCap (hK : IsCap K (π / 2)) : armFm K 0 = 1 := by
  rw [armFm_eq, zero_add, hK.supportFn_pi_div_two, edgeMin_zero_of_isCap hK, sub_zero]

theorem armFp_zero_eq (hK : IsCap K (π / 2)) : armFp K 0 = 1 - edgeLength K 0 := by
  rw [armFp_eq, zero_add, hK.supportFn_pi_div_two, edgeLength,
    edgeMin_zero_of_isCap hK, sub_zero]

/-! ## The crude niche-side bound (no neighbouring angles needed) -/

theorem actR_subset_cross_or_le {Θ : Finset ℝ} (hΘ : Θ.Nonempty) (h : ℝ → ℝ) (t : ℝ) :
    {x : ℝ | roofR Θ hΘ h x = wall h t x}
      ⊆ crossSet Θ h t ∪ {x : ℝ | wall h t x ≤ wall h (t + π / 2) x} := by
  intro x hx
  have hx' : roofR Θ hΘ h x = wall h t x := hx
  rcases le_or_gt (wall h t x) (wall h (t + π / 2) x) with hdt | hdt
  · exact Or.inr hdt
  · obtain ⟨s, hs, hseq⟩ := Finset.exists_mem_eq_sup' hΘ
      (fun s => min (wall h s x) (wall h (s + π / 2) x))
    have hsup : roofR Θ hΘ h x = min (wall h s x) (wall h (s + π / 2) x) := hseq
    rw [hx'] at hsup
    have hst : s ≠ t := by
      intro heq
      rw [heq, min_eq_right hdt.le] at hsup
      exact hdt.ne hsup.symm
    have hmin : min (wall h s x) (wall h (s + π / 2) x) = wall h t x := hsup.symm
    refine Or.inl (mem_biUnion (Finset.mem_erase.2 ⟨hst, hs⟩) ?_)
    rcases min_cases (wall h s x) (wall h (s + π / 2) x) with ⟨he, -⟩ | ⟨he, -⟩
    · exact Or.inl (he.symm.trans hmin)
    · exact Or.inr (he.symm.trans hmin)

/-- **The crude niche-side bound.**  For *every* angle `t ∈ Θ` of a polygon cap,

    `τ(t) ≤ ((h(t) − 1)·tan t + (h(t + π/2) − 1))⁺`.

Geometrically: the niche side with normal `t` lies above the fan floor `y = 0` and (off a null
set of accidental crossings) below the inner wall `d_t`, so its `x`-projection is contained in an
interval of length `sin t · ((h(t)−1) tan t + (h(t+π/2)−1))`.  **No neighbouring angles are
needed**, which is what makes this usable at the endpoint angle `t = δ`. -/
theorem tauH_le_crude {Θ : Finset ℝ} (hP : PolySetup (π / 2) Θ) {K : Set ℝ²}
    (hK : IsPolyCap (π / 2) Θ K) {t : ℝ} (ht : t ∈ Θ) :
    tauH (π / 2) Θ hP.nonempty (supportFn K) t
      ≤ max 0 ((supportFn K t - 1) * tan t + (supportFn K (t + π / 2) - 1)) := by
  have hpi := pi_gt_three
  set h := supportFn K with hh
  obtain ⟨ht0, ht2⟩ := hP.angles.2 t ht
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 (by linarith)
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith, ht2⟩
  have hsp : 0 < sin (t + π / 2) := by rwa [sin_add_pi_div_two]
  set c₁ : ℝ := h t - 1 with hc1
  set c₂ : ℝ := h (t + π / 2) - 1 with hc2
  set A : ℝ := cos t * c₁ - sin t * c₂ with hAdef
  set B : ℝ := c₁ / cos t with hBdef
  have hfloor : ∀ x : ℝ, floorF (π / 2) h x = 0 := by
    intro x
    rw [floorF_pi_div_two, hh, hK.1.supportFn_pi_div_two, sub_self, lineFn,
      cos_pi_div_two, mul_zero, zero_sub, neg_zero, zero_div]
  have hsub : actR Θ hP.nonempty h t ∩ posR (π / 2) Θ hP.nonempty h
      ⊆ crossSet Θ h t ∪ Icc A B := by
    rintro x ⟨hact, hpos⟩
    have hact' : roofR Θ hP.nonempty h x = wall h t x := hact
    have hposx : (0 : ℝ) < wall h t x := by
      have hp : floorF (π / 2) h x < roofR Θ hP.nonempty h x := hpos
      rw [hfloor x, hact'] at hp
      exact hp
    have hxB : x ≤ B := by
      have hw : wall h t x = (c₁ - x * cos t) / sin t := rfl
      rw [hw, lt_div_iff₀ hst, zero_mul, sub_pos] at hposx
      rw [hBdef, le_div_iff₀ hct]
      linarith
    rcases actR_subset_cross_or_le hP.nonempty h t hact' with hc | hle
    · exact Or.inl hc
    · refine Or.inr ⟨?_, hxB⟩
      have hle' : lineFn t c₁ x ≤ lineFn (t + π / 2) c₂ x := hle
      rw [lineFn_le_lineFn_iff hst hsp, show t - (t + π / 2) = -(π / 2) by ring,
        Real.sin_neg, sin_pi_div_two, sin_add_pi_div_two] at hle'
      rw [hAdef]
      linarith
  have hcross : volume (crossSet Θ h t) = 0 := volume_crossSet hP.angles.2 h ht
  have hvol : volume (actR Θ hP.nonempty h t ∩ posR (π / 2) Θ hP.nonempty h)
      ≤ ENNReal.ofReal (B - A) := by
    refine le_trans (measure_mono hsub) (le_trans (measure_union_le _ _) ?_)
    rw [hcross, zero_add, Real.volume_Icc]
  have htoReal : (ENNReal.ofReal (B - A)).toReal = max (B - A) 0 := ENNReal.toReal_ofReal'
  have hreal : volume.real (actR Θ hP.nonempty h t ∩ posR (π / 2) Θ hP.nonempty h)
      ≤ max (B - A) 0 := by
    rw [measureReal_def, ← htoReal]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
  have hkey : B - A = (c₁ * tan t + c₂) * sin t := by
    have hc : cos t ≠ 0 := ne_of_gt hct
    have h1 : (B - A) * cos t = c₁ * sin t ^ 2 + c₂ * sin t * cos t := by
      rw [hBdef, hAdef, sub_mul, div_mul_cancel₀ _ hc]
      linear_combination (-c₁) * sin_sq_add_cos_sq t
    have h2 : ((c₁ * tan t + c₂) * sin t) * cos t = c₁ * sin t ^ 2 + c₂ * sin t * cos t := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
    exact mul_right_cancel₀ hc (h1.trans h2.symm)
  have hfin : max (B - A) 0 ≤ max 0 (c₁ * tan t + c₂) * sin t := by
    rcases le_or_gt 0 (c₁ * tan t + c₂) with hge | hlt
    · rw [max_eq_left (by rw [hkey]; exact mul_nonneg hge hst.le), max_eq_right hge, hkey]
    · rw [max_eq_right (by rw [hkey]; nlinarith), max_eq_left hlt.le, zero_mul]
  rw [tauH_eq_pi_div_two hP.nonempty h ht0 ht2, div_le_iff₀ hst]
  linarith

/-- **Theorem 6.3.3 at an endpoint angle.**  Combining the balanced condition (Thm 3.4.9) with
`tauH_le_crude`, the edge length of a maximum polygon cap at *any* `t ∈ Θ` obeys

    `|e_K(t)| ≤ ((h_K(t) − 1)·tan t + (h_K(t + π/2) − 1))⁺`.

This is the bound Baek's Theorem 6.3.3 does not provide at `t = δ` and `t = (n−1)δ`. -/
theorem edgeLength_le_crude {Θ : Finset ℝ} (hP : PolySetup (π / 2) Θ) {K : Set ℝ²}
    (hK : IsMaxPolyCap (π / 2) Θ K) {t : ℝ} (ht : t ∈ Θ) :
    edgeLength K t
      ≤ max 0 ((supportFn K t - 1) * tan t + (supportFn K (t + π / 2) - 1)) := by
  refine le_trans (edgeLength_le_sigmaH hP hK.1 ht) ?_
  rw [IsMaxPolyCap.balanced hP hK (Finset.mem_union_left _ (Finset.mem_union_left _ ht))]
  exact tauH_le_crude hP hK.1 ht

/-! ## `arcFn K 0 = 0` for a maximum polygon cap -/

section Uniform

variable {n : ℕ} (hn : 1 < n)

include hn

lemma uniform_no_normal_zero :
    ∀ r ∈ polyCapFin (π / 2) (uniformAngles (π / 2) n), u r ≠ u 0 := by
  have hpi := pi_pos
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn.le
  have hδ0 : 0 < (π / 2) / n := by positivity
  intro r hr
  rcases mem_polyCapFin.1 hr with hΘ | ⟨q, hq, rfl⟩ | rfl | rfl | rfl | rfl
  · obtain ⟨i, hi0, hin, rfl⟩ := mem_uniformAngles_iff.1 hΘ
    have hi0' : (0:ℝ) < (i : ℝ) := by exact_mod_cast hi0
    have hin' : (i : ℝ) < (n : ℝ) := by exact_mod_cast hin
    have hlt : (i : ℝ) * ((π / 2) / n) < π / 2 := by
      rw [mul_div_assoc', div_lt_iff₀ hn0]; nlinarith
    exact u_ne_u_of_sub_lt (by nlinarith [mul_pos hi0' hδ0]) (by nlinarith) (by nlinarith)
  · obtain ⟨i, hi0, hin, rfl⟩ := mem_uniformAngles_iff.1 hq
    have hi0' : (0:ℝ) < (i : ℝ) := by exact_mod_cast hi0
    have hin' : (i : ℝ) < (n : ℝ) := by exact_mod_cast hin
    have hlt : (i : ℝ) * ((π / 2) / n) < π / 2 := by
      rw [mul_div_assoc', div_lt_iff₀ hn0]; nlinarith
    exact u_ne_u_of_sub_lt (by nlinarith [mul_pos hi0' hδ0]) (by nlinarith) (by nlinarith)
  · exact u_ne_u_of_sub_lt (by nlinarith) (by nlinarith) (by nlinarith)
  · exact u_ne_u_of_sub_lt (by nlinarith) (by nlinarith) (by nlinarith)
  · exact u_ne_u_of_sub_lt (by nlinarith) (by nlinarith) (by nlinarith)
  · exact u_ne_u_of_sub_lt (by nlinarith) (by nlinarith) (by nlinarith)

theorem edgeLength_zero_of_maxPolyCap {K : Set ℝ²}
    (hK : IsMaxPolyCap (π / 2) (uniformAngles (π / 2) n) K) : edgeLength K 0 = 0 := by
  have hpi := pi_pos
  have hP : PolySetup (π / 2) (uniformAngles (π / 2) n) :=
    ⟨by linarith, le_rfl, uniformAngles_isAngleSet (by linarith) hn⟩
  exact edgeLength_eq_zero_of_no_normal hK.1.1.isCompact hK.1.1.nonempty hK.1.1.convex
    (IsPolyCap.eq_iInter_fin hK.1) (uniform_no_normal_zero hn) (width_pos_of_isMaxPolyCap hP hK 0)

/-- `arcFn K 0 = e^{max}_K(0) = e^{min}_K(0) + |e_K(0)| = 0`. -/
theorem arcFn_zero_of_maxPolyCap {K : Set ℝ²}
    (hK : IsMaxPolyCap (π / 2) (uniformAngles (π / 2) n) K) : arcFn K 0 = 0 := by
  have h0 : edgeMax K 0 = 0 := by
    have h1 := edgeLength_zero_of_maxPolyCap hn hK
    have h2 := edgeMin_zero_of_isCap hK.1.1
    rw [edgeLength, h2, sub_zero] at h1
    exact h1
  rw [arcFn, inner_vtxP_v, h0, intervalIntegral.integral_same, add_zero]

/-! ## The `O(δ)` bound at the endpoint angle `δ`, and Equation (6.5) from `0` -/

theorem edgeLength_delta_le {K : Set ℝ²}
    (hK : IsMaxPolyCap (π / 2) (uniformAngles (π / 2) n) K)
    {R : ℝ} (hR : ∀ p ∈ K, ‖p‖ ≤ R) (hδ1 : (π / 2) / n ≤ 1) :
    edgeLength K ((π / 2) / n) ≤ (3 * R + 2) * ((π / 2) / n) := by
  have hpi := pi_gt_three
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn.le
  set δ : ℝ := (π / 2) / n with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hKc := hK.1.1.isCompact
  have hKne := hK.1.1.nonempty
  have hR0 : (0:ℝ) ≤ R := by
    obtain ⟨z, hz⟩ := hKne
    exact le_trans (norm_nonneg z) (hR z hz)
  have hP : PolySetup (π / 2) (uniformAngles (π / 2) n) :=
    ⟨by linarith, le_rfl, uniformAngles_isAngleSet (by linarith) hn⟩
  have hδΘ : δ ∈ uniformAngles (π / 2) n :=
    mem_uniformAngles_iff.2 ⟨1, one_pos, hn, by rw [hδdef]; push_cast; ring⟩
  have hmain := edgeLength_le_crude hP hK hδΘ
  -- bound the three ingredients
  have hsup : |supportFn K δ| ≤ R := abs_supportFn_le hKc hKne hR δ
  have hsq : δ ^ 2 ≤ δ := by nlinarith [hδ0, hδ1]
  have hcube : δ ^ 3 ≤ δ := by nlinarith [hδ0, hδ1, hsq]
  have htan : tan δ ≤ 2 * δ := by
    rw [Real.tan_eq_sin_div_cos]
    linarith [tan_le_add_cube hδ0 hδ1]
  have htan0 : 0 ≤ tan δ := by
    rw [Real.tan_eq_sin_div_cos]
    have hcd : 0 < cos δ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hsd : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδ0 (by linarith)
    positivity
  have hlip : |supportFn K (δ + π / 2) - supportFn K (π / 2)| ≤ R * |δ + π / 2 - (π / 2)| :=
    abs_supportFn_sub_le hKc hKne hR (δ + π / 2) (π / 2)
  rw [show δ + π / 2 - (π / 2) = δ by ring, abs_of_pos hδ0, hK.1.1.supportFn_pi_div_two] at hlip
  have h2 : supportFn K (δ + π / 2) - 1 ≤ R * δ := by
    have := (abs_le.1 hlip).2; linarith
  have h1 : (supportFn K δ - 1) * tan δ ≤ (R + 1) * (2 * δ) := by
    have ha : supportFn K δ - 1 ≤ R + 1 := by linarith [(abs_le.1 hsup).2]
    have hb : (supportFn K δ - 1) * tan δ ≤ (R + 1) * tan δ :=
      mul_le_mul_of_nonneg_right ha htan0
    nlinarith [htan, hR0]
  refine hmain.trans (max_le (by positivity) ?_)
  linarith

/-- **Equation (6.5) starting from `0`.**  For a maximum polygon cap with `n` steps
(`δ = (π/2)/n`) and `2 ≤ c`, `c + 2 ≤ n`:

    `arcFn K (c δ) ≤ (1 + 2R)·(c δ) + ((3R+2) + (6+4R)(π/2))·δ`.

The first step `(0, δ]` uses the new endpoint bound `edgeLength_delta_le`; the rest is
`sigmaK_Ioc_le_integral_poly` with `m = 1`. -/
theorem arcFn_le_of_maxPolyCap {K : Set ℝ²}
    (hK : IsMaxPolyCap (π / 2) (uniformAngles (π / 2) n) K)
    {R : ℝ} (hR : ∀ p ∈ K, ‖p‖ ≤ R) (hδ1 : (π / 2) / n ≤ 1)
    {c : ℕ} (hc : 2 ≤ c) (hcn : c + 2 ≤ n) :
    arcFn K ((c : ℝ) * ((π / 2) / n))
      ≤ (1 + 2 * R) * ((c : ℝ) * ((π / 2) / n))
        + ((3 * R + 2) + (6 + 4 * R) * (π / 2)) * ((π / 2) / n) := by
  have hpi := pi_gt_three
  have hn0 : (0:ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn.le
  set δ : ℝ := (π / 2) / n with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hnδ : (n : ℝ) * δ = π / 2 := by rw [hδdef]; field_simp
  have hKc := hK.1.1.isCompact
  have hKne := hK.1.1.nonempty
  have hR0 : (0:ℝ) ≤ R := by
    obtain ⟨z, hz⟩ := hKne
    exact le_trans (norm_nonneg z) (hR z hz)
  have hconv := hK.1.1.convex
  have hA := IsPolyCap.eq_iInter_fin hK.1
  have hP : PolySetup (π / 2) (uniformAngles (π / 2) n) :=
    ⟨by linarith, le_rfl, uniformAngles_isAngleSet (by linarith) hn⟩
  have hwidth := width_pos_of_isMaxPolyCap hP hK
  have harc0 : arcFn K 0 = 0 := arcFn_zero_of_maxPolyCap hn hK
  have hcR : (1:ℝ) ≤ (c : ℝ) := by exact_mod_cast Nat.one_le_of_lt (Nat.lt_of_lt_of_le one_lt_two hc)
  have hcn' : (c : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hcn
  -- Step 1: the first cell `(0, δ]`
  have hstep1 : arcFn K δ ≤ (3 * R + 2) * δ := by
    have hgap : ∀ s ∈ Ioo (0:ℝ) δ, ∀ r ∈ polyCapFin (π / 2) (uniformAngles (π / 2) n),
        u r ≠ u s := by
      have h := uniform_gap_base hn (j := 0) (by omega)
      intro s hs r hr
      refine h s ?_ r hr
      simpa using hs
    have heq := sigmaK_Ioc_eq_singleton_of_gap hKc hKne hconv hA hwidth hδ0 hgap
    have h1 : (sigmaK K (Ioc 0 δ)).toReal = arcFn K δ - arcFn K 0 :=
      sigmaK_Ioc_toReal hKc hKne hδ0.le
    rw [heq, sigmaK_singleton hKc hKne,
      ENNReal.toReal_ofReal (edgeLength_nonneg hKc hKne δ), harc0, sub_zero] at h1
    rw [← h1]
    exact edgeLength_delta_le hn hK hR hδ1
  -- Step 2: the cells `(δ, cδ]`
  have hmain := sigmaK_Ioc_le_integral_poly hn hK hR hδ1 (m := 1) (N := c - 1)
    le_rfl (by omega)
  have hcast : ((1 : ℕ) : ℝ) + ((c - 1 : ℕ) : ℝ) = (c : ℝ) := by
    have : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
      have : (1 : ℕ) ≤ c := by omega
      push_cast [Nat.cast_sub this]; ring
    rw [this]; push_cast; ring
  rw [hcast, Nat.cast_one, one_mul, ← hδdef] at hmain
  have htoReal : (sigmaK K (Ioc δ ((c : ℝ) * δ))).toReal = arcFn K ((c : ℝ) * δ) - arcFn K δ :=
    sigmaK_Ioc_toReal hKc hKne (by nlinarith)
  rw [htoReal] at hmain
  -- bound the integral and the error
  have hbd : ∀ r : ℝ, k0 (armGp K r) ≤ 1 + 2 * R :=
    fun r => (k0_le_one_add_abs _).trans (by linarith [abs_armGp_le hKc hKne hR r])
  have hint : IntervalIntegrable (fun r => k0 (armGp K r)) volume δ ((c : ℝ) * δ) :=
    intervalIntegrable_k0_comp (intervalIntegrable_armGp hKc hKne _ _)
  have hI := intervalIntegral.integral_mono_on (by nlinarith : δ ≤ (c : ℝ) * δ) hint
    (intervalIntegrable_const (μ := volume) (c := 1 + 2 * R)) fun r _ => hbd r
  rw [intervalIntegral.integral_const, smul_eq_mul] at hI
  have herr : ((c - 1 : ℕ) : ℝ) * ((6 + 4 * R) * δ ^ 2) ≤ (6 + 4 * R) * (π / 2) * δ := by
    have hc1 : ((c - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : c - 1 ≤ n)
    have h6 : (0:ℝ) ≤ 6 + 4 * R := by linarith
    have hcd : ((c - 1 : ℕ) : ℝ) * δ ≤ π / 2 := by
      rw [← hnδ]
      exact mul_le_mul_of_nonneg_right hc1 hδ0.le
    calc ((c - 1 : ℕ) : ℝ) * ((6 + 4 * R) * δ ^ 2)
        = ((6 + 4 * R) * δ) * (((c - 1 : ℕ) : ℝ) * δ) := by ring
      _ ≤ ((6 + 4 * R) * δ) * (π / 2) :=
          mul_le_mul_of_nonneg_left hcd (mul_nonneg h6 hδ0.le)
      _ = (6 + 4 * R) * (π / 2) * δ := by ring
  linarith

end Uniform

/-! ## `σ_K({0}) = 0` and `f⁺_K(0) = 1` for a balanced maximum cap -/

/-- **`σ_K({0}) = 0`.**  `arcFn K 0 = e^{max}_K(0) = |e_K(0)|` (because `e^{min}_K(0) = 0`), and
`arcFn K 0 ≤ arcFn K b ≤ (1 + 2R)·b` for every dyadic `b = (π/2)/2^k`, by `arcFn_le_of_maxPolyCap`
and the Hausdorff limit.  Letting `b → 0` gives `|e_K(0)| ≤ 0`. -/
theorem edgeLength_zero_of_balanced (hK : IsBalancedMaxCap K (π / 2)) : edgeLength K 0 = 0 := by
  have hpi := pi_gt_three
  have hcap := hK.1
  have hKc := hcap.isCompact
  have hKne := hcap.nonempty
  obtain ⟨n, Ks, hmono, hn2, hmax, hlim⟩ := hK.2
  have hKsc : ∀ i, IsCompact (Ks i) := fun i => (hmax i).1.1.isCompact
  have hKsne : ∀ i, (Ks i).Nonempty := fun i => (hmax i).1.1.nonempty
  obtain ⟨R, hR⟩ := exists_eventually_norm_le hKsc hKsne hKc hKne hlim
  have hR0 : (0:ℝ) ≤ R := by
    obtain ⟨i, hi⟩ := hR.exists
    obtain ⟨z, hz⟩ := hKsne i
    exact le_trans (norm_nonneg z) (hi z hz)
  set CR : ℝ := (3 * R + 2) + (6 + 4 * R) * (π / 2) with hCR
  have hCR0 : (0:ℝ) ≤ CR := by rw [hCR]; nlinarith
  -- the dyadic bound
  have key : ∀ k : ℕ, 1 ≤ k → arcFn K ((π / 2) / 2 ^ k) ≤ (1 + 2 * R) * ((π / 2) / 2 ^ k) := by
    intro k hk
    have hMpos : (0:ℝ) < (2:ℝ) ^ k := by positivity
    set b : ℝ := (π / 2) / 2 ^ k with hbdef
    have hb0 : 0 < b := by rw [hbdef]; positivity
    have h2k : (2:ℝ) ≤ (2:ℝ) ^ k := by
      calc (2:ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
    have hb2 : b < π / 2 := by
      rw [hbdef, div_lt_iff₀ hMpos]
      nlinarith
    have hdb : edgeLength K b = 0 := edgeLength_eq_zero_of_balanced hK hb0 hb2
    have hlimarc := tendsto_arcFn_of_tendsto_hausdorffDist hKsc hKsne hKc hKne hlim hdb
    have hn_top : Tendsto (fun i => ((n i : ℝ))) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hmono.tendsto_atTop
    have hdiv : Tendsto (fun i => (π / 2) / ((n i : ℕ) : ℝ)) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds hn_top
    have hrhs : Tendsto (fun i => (1 + 2 * R) * b + CR * ((π / 2) / ((n i : ℕ) : ℝ))) atTop
        (𝓝 ((1 + 2 * R) * b + CR * 0)) := tendsto_const_nhds.add (hdiv.const_mul CR)
    rw [mul_zero, add_zero] at hrhs
    refine le_of_tendsto_of_tendsto hlimarc hrhs ?_
    filter_upwards [hR, eventually_ge_atTop (2 ^ (k + 1))] with i hRi hik
    have hn1 : 1 < n i := (hn2 i).1
    have hni : 2 ^ (k + 1) ≤ n i := le_trans hik hmono.le_apply
    obtain ⟨ki, hki⟩ := (hn2 i).2
    have hkki : k + 1 ≤ ki := by
      have h2 : (2:ℕ) ^ (k + 1) ≤ 2 ^ ki := by rw [← hki]; exact hni
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
    set c : ℕ := 2 ^ (ki - k) with hcdef
    have hnc : n i = 2 ^ k * c := by
      rw [hki, hcdef, ← pow_add]; congr 1; omega
    have hc2 : 2 ≤ c := by
      rw [hcdef]
      calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (ki - k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hcn : c + 2 ≤ n i := by
      rw [hnc]
      have h2k' : (2:ℕ) ≤ 2 ^ k := by
        calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      nlinarith [hc2, h2k']
    have hn0 : (0:ℝ) < (n i : ℝ) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1.le
    have hncR : ((n i : ℕ) : ℝ) = 2 ^ k * (c : ℝ) := by rw [hnc]; push_cast; ring
    have hδ1 : (π / 2) / ((n i : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hn0]
      have h2n : (2:ℝ) ≤ (n i : ℝ) := by exact_mod_cast hn1
      linarith [Real.pi_le_four]
    have hbeq : ((c : ℕ) : ℝ) * ((π / 2) / ((n i : ℕ) : ℝ)) = b := by
      rw [hbdef, hncR]
      have hc0 : (0:ℝ) < (c : ℝ) := by
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hc2
      field_simp
    have h := arcFn_le_of_maxPolyCap hn1 (hmax i) hRi hδ1 hc2 hcn
    rw [hbeq] at h
    exact h
  -- let `b → 0`
  have harc0 : arcFn K 0 ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hcpos : 0 < ε / ((1 + 2 * R) * (π / 2)) := by positivity
    obtain ⟨k, hkk⟩ := exists_pow_lt_of_lt_one hcpos (by norm_num : (1:ℝ) / 2 < 1)
    have hMpos : (0:ℝ) < (2:ℝ) ^ (k + 1) := by positivity
    have hkM : 1 / (2:ℝ) ^ (k + 1) < ε / ((1 + 2 * R) * (π / 2)) := by
      rw [div_pow, one_pow] at hkk
      have : (2:ℝ) ^ k ≤ 2 ^ (k + 1) := by
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have h2k : (0:ℝ) < (2:ℝ) ^ k := by positivity
      calc 1 / (2:ℝ) ^ (k + 1) ≤ 1 / (2:ℝ) ^ k := by
            apply one_div_le_one_div_of_le h2k this
        _ < ε / ((1 + 2 * R) * (π / 2)) := hkk
    have hmono' : arcFn K 0 ≤ arcFn K ((π / 2) / 2 ^ (k + 1)) :=
      arcFn_mono hKc hKne (by positivity)
    have hkey := key (k + 1) (by omega)
    have hlt : (1 + 2 * R) * ((π / 2) / 2 ^ (k + 1)) < ε := by
      have hD : (0:ℝ) < (1 + 2 * R) * (π / 2) := by nlinarith [hR0, hpi]
      rw [div_lt_div_iff₀ hMpos hD] at hkM
      rw [show (1 + 2 * R) * ((π / 2) / (2:ℝ) ^ (k + 1))
          = ((1 + 2 * R) * (π / 2)) / 2 ^ (k + 1) by ring, div_lt_iff₀ hMpos]
      linarith
    linarith
  -- conclude
  have harcEq : arcFn K 0 = edgeLength K 0 := by
    rw [arcFn, inner_vtxP_v, intervalIntegral.integral_same, add_zero, edgeLength,
      edgeMin_zero_of_isCap hcap, sub_zero]
  rw [harcEq] at harc0
  exact le_antisymm harc0 (edgeLength_nonneg hKc hKne 0)

/-- **`f⁺_K(0) = 1`** for every balanced maximum cap — the input Baek's Lemma 6.5.2 needs and the
paper only asserts informally (§1.7.3). -/
theorem armFp_zero_of_balanced (hK : IsBalancedMaxCap K (π / 2)) : armFp K 0 = 1 := by
  rw [armFp_zero_eq hK.1, edgeLength_zero_of_balanced hK, sub_zero]

/-- **Baek Theorem 6.5.1, unconditional form**: `1 + ∫_0^T m₀(g⁺_K) ≤ f⁺_K(T)`. -/
theorem one_add_integral_le_armFp (hK : IsBalancedMaxCap K (π / 2)) {T : ℝ}
    (hT0 : 0 < T) (hT2 : T < π / 2) :
    1 + ∫ s in (0:ℝ)..T, m0 (armGp K s) ≤ armFp K T := by
  have h := armFp_ge_balanced hK hT0 hT2
  rwa [armFp_zero_of_balanced hK] at h

end Sofa
