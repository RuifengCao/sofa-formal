/-
# Sofa/Width.lean — the width of `P_ω \ Δ_ω` (Baek §1.5.1, the geometric half of Thm 1.5.2)

Writing `p = a u₀ + b v_ω` (a basis for `ω ≠ π/2`), the parallelogram becomes a square
`P_ω = {0 ≤ a, b ≤ sec ω}` and the triangle `Δ_ω` becomes the simplex `{a, b ≥ 0, a + b ≤ c_ω}`.

* `mem_niche_of_coord_lt`: the open simplex is inside `N(K)` (via Theorem 4.2.5);
* `width_le_one`: `P_ω \ Δ_ω` has width `≤ 1` in every direction `u_t`, `t ∈ [ω, π/2]` —
  the two cases of the computation collapse to `sin t ≤ 1` and `cos (t − ω) ≤ 1`.

STATUS: [PROOF-C-local] round 1 (2026-09-17, Opus 5): compiled in the cloud dev tree, no `sorry`.
-/
import Sofa.RightAngle

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {ω : ℝ} {K : Set ℝ²}

/-! ## The `(u₀, v_ω)` coordinates -/

/-- The `u₀`-coordinate of `p` in the basis `(u₀, v_ω)`. -/
def coA (ω : ℝ) (p : ℝ²) : ℝ := ⟪p, u ω⟫ / cos ω

/-- The `v_ω`-coordinate of `p` in the basis `(u₀, v_ω)`. -/
def coB (ω : ℝ) (p : ℝ²) : ℝ := p 1 / cos ω

lemma inner_u_zero_u (t : ℝ) : ⟪u 0, u t⟫ = cos t := by
  rw [inner_u_u_eq_cos, zero_sub, cos_neg]

/-- The decomposition of `⟪p, u_t⟫` in the `(u₀, v_ω)` coordinates. -/
lemma inner_eq_coord (hcos : cos ω ≠ 0) (p : ℝ²) (t : ℝ) :
    ⟪p, u t⟫ = coA ω p * cos t + coB ω p * sin (t - ω) := by
  rw [coA, coB, inner_u_decomp, inner_u_decomp, sin_sub]
  field_simp
  ring

lemma coA_nonneg_of_mem_para (hp : p ∈ para ω) (hcos : 0 < cos ω) : 0 ≤ coA ω p :=
  div_nonneg (mem_para_iff.1 hp).2.1 hcos.le

lemma coB_nonneg_of_mem_para (hp : p ∈ para ω) (hcos : 0 < cos ω) : 0 ≤ coB ω p :=
  div_nonneg (mem_para_iff.1 hp).1.1 hcos.le

lemma coA_le_of_mem_para (hp : p ∈ para ω) (hcos : 0 < cos ω) : coA ω p ≤ 1 / cos ω := by
  rw [coA, div_le_div_iff_of_pos_right hcos]
  exact (mem_para_iff.1 hp).2.2

lemma coB_le_of_mem_para (hp : p ∈ para ω) (hcos : 0 < cos ω) : coB ω p ≤ 1 / cos ω := by
  rw [coB, div_le_div_iff_of_pos_right hcos]
  exact (mem_para_iff.1 hp).1.2

/-! ## The open simplex is inside the niche -/

/-- **Consequence of Theorem 4.2.5.** The open simplex `{a, b ≥ 0, a + b < c_ω}` (i.e. the
interior of `Δ_ω` together with its two legs) lies inside `N(K)`. -/
theorem mem_niche_of_coord_lt (hω0 : 0 < ω) (hω1 : ω < π / 2) (hcos : cos ω ≤ 5 / 11)
    (hK : IsBalancedMaxCap K ω) (harea : 11 / 5 ≤ volume.real K)
    {p : ℝ²} (ha : 0 ≤ coA ω p) (hb : 0 ≤ coB ω p) (hab : coA ω p + coB ω p < cw ω) :
    p ∈ niche K ω := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  have hcw0 : 0 < cw ω := by
    rw [cw]
    exact div_pos (by nlinarith [sin_le_one ω, mul_pos hcω hcω, sin_sq_add_cos_sq ω]) hcω
  obtain ⟨t, ht, hw⟩ := exists_wedge hω0 hω1 hcos hK harea
  have hct : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
  have hst : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, pi_pos])
  have hctω : 0 < cos (t - ω) :=
    cos_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2, pi_pos]⟩
  have hstω : sin (t - ω) ≤ 0 :=
    sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [ht.2]) (by linarith [ht.1, pi_pos])
  -- the three vertices
  have hv1 := hw 0 (Or.inl rfl)
  have hv2 := hw (cw ω • u 0) (Or.inr (Or.inl rfl))
  have hv3 := hw (cw ω • v ω) (Or.inr (Or.inr rfl))
  rw [inner_zero_left, inner_zero_left] at hv1
  rw [real_inner_smul_left, real_inner_smul_left, inner_u_zero_u, inner_u_zero_u] at hv2
  rw [real_inner_smul_left, real_inner_smul_left, inner_v_u_eq_sin, inner_v_u_eq_sin] at hv3
  rw [show t + π / 2 - ω = (t - ω) + π / 2 by ring, sin_add_pi_div_two] at hv3
  rw [cos_add_pi_div_two] at hv2
  refine mem_niche_iff.2 ⟨⟨?_, ?_⟩, t, ht, ?_⟩
  · have : p 1 = coB ω p * cos ω := by rw [coB]; field_simp
    rw [this]; positivity
  · have : ⟪p, u ω⟫ = coA ω p * cos ω := by rw [coA]; field_simp
    rw [this]; positivity
  · rw [mem_QminusS_iff, inner_eq_coord hcω.ne' p t, inner_eq_coord hcω.ne' p (t + π / 2),
      show t + π / 2 - ω = (t - ω) + π / 2 by ring, sin_add_pi_div_two, cos_add_pi_div_two]
    constructor
    · nlinarith [hv2.1, hv3.1, mul_nonpos_of_nonneg_of_nonpos hb hstω]
    · nlinarith [hv2.2, hv3.2, mul_nonneg ha hst.le]

/-! ## The width bound -/

/-- **The width bound.** For `p, q ∈ P_ω` with `q` outside the open simplex `Δ_ω`, the extent of
`{p, q}` in the direction `u_t` is at most `1`, for every `t ∈ [ω, π/2]`. -/
theorem width_le_one (hω0 : 0 < ω) (hω1 : ω < π / 2) {p q : ℝ²}
    (hp : p ∈ para ω) (hq : q ∈ para ω) (hqT : cw ω ≤ coA ω q + coB ω q)
    {t : ℝ} (ht1 : ω ≤ t) (ht2 : t ≤ π / 2) : ⟪p - q, u t⟫ ≤ 1 := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  have hct : 0 ≤ cos t := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], ht2⟩
  have hst : 0 ≤ sin (t - ω) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
  have hpa := coA_le_of_mem_para hp hcω
  have hpb := coB_le_of_mem_para hp hcω
  have hqa := coA_nonneg_of_mem_para hq hcω
  have hqb := coB_nonneg_of_mem_para hq hcω
  rw [inner_sub_left, inner_eq_coord hcω.ne' p t, inner_eq_coord hcω.ne' q t]
  have h1 : coA ω p * cos t + coB ω p * sin (t - ω)
      ≤ 1 / cos ω * cos t + 1 / cos ω * sin (t - ω) := by nlinarith
  rcases le_total (cos t) (sin (t - ω)) with hle | hle
  · have hid : 1 / cos ω * cos t + 1 / cos ω * sin (t - ω) - cw ω * cos t = sin t := by
      rw [cw, sin_sub]
      field_simp
      ring
    have h2 : cw ω * cos t ≤ coA ω q * cos t + coB ω q * sin (t - ω) := by nlinarith
    linarith [sin_le_one t]
  · have hid : 1 / cos ω * cos t + 1 / cos ω * sin (t - ω) - cw ω * sin (t - ω)
        = cos (t - ω) := by
      rw [cw, sin_sub, cos_sub]
      field_simp
      nlinarith [sin_sq_add_cos_sq ω]
    have h2 : cw ω * sin (t - ω) ≤ coA ω q * cos t + coB ω q * sin (t - ω) := by nlinarith
    linarith [cos_le_one (t - ω)]

/-! ## The width of a balanced maximum sofa -/

/-- Points of `K ∖ N(K)` lie outside the open simplex. -/
theorem cw_le_coord_of_not_mem_niche (hω0 : 0 < ω) (hω1 : ω < π / 2) (hcos : cos ω ≤ 5 / 11)
    (hK : IsBalancedMaxCap K ω) (harea : 11 / 5 ≤ volume.real K)
    {q : ℝ²} (hq : q ∈ K) (hqn : q ∉ niche K ω) : cw ω ≤ coA ω q + coB ω q := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  by_contra hcon
  push Not at hcon
  exact hqn (mem_niche_of_coord_lt hω0 hω1 hcos hK harea
    (coA_nonneg_of_mem_para (hK.1.subset_para hq) hcω)
    (coB_nonneg_of_mem_para (hK.1.subset_para hq) hcω) hcon)

/-- **The width bound for a balanced maximum sofa.** Any `S ⊆ K ∖ N(K)` has width `≤ 1` in every
direction `u_t` with `t ∈ [ω, π/2]`. -/
theorem inner_sub_le_one_of_subset (hω0 : 0 < ω) (hω1 : ω < π / 2) (hcos : cos ω ≤ 5 / 11)
    (hK : IsBalancedMaxCap K ω) (harea : 11 / 5 ≤ volume.real K)
    {S : Set ℝ²} (hS : S ⊆ K \ niche K ω) {t : ℝ} (ht1 : ω ≤ t) (ht2 : t ≤ π / 2)
    {p q : ℝ²} (hp : p ∈ S) (hq : q ∈ S) : ⟪p - q, u t⟫ ≤ 1 := by
  have hcω : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hω1⟩
  exact width_le_one hω0 hω1 (hK.1.subset_para (hS hp).1) (hK.1.subset_para (hS hq).1)
    (cw_le_coord_of_not_mem_niche hω0 hω1 hcos hK harea (hS hq).1 (hS hq).2) ht1 ht2

/-- The same, in terms of support functions: `h_S(t) + h_S(t + π) ≤ 1`. -/
theorem supportFn_add_supportFn_le_one (hω0 : 0 < ω) (hω1 : ω < π / 2) (hcos : cos ω ≤ 5 / 11)
    (hK : IsBalancedMaxCap K ω) (harea : 11 / 5 ≤ volume.real K)
    {S : Set ℝ²} (hS : S ⊆ K \ niche K ω) (hSc : IsCompact S) (hSne : S.Nonempty)
    {t : ℝ} (ht1 : ω ≤ t) (ht2 : t ≤ π / 2) : supportFn S t + supportFn S (t + π) ≤ 1 := by
  obtain ⟨p, hp, hpv⟩ := exists_supportFn_eq hSc hSne t
  obtain ⟨q, hq, hqv⟩ := exists_supportFn_eq hSc hSne (t + π)
  rw [← hpv, ← hqv, u_add_pi, inner_neg_right, ← sub_eq_add_neg, ← inner_sub_left]
  exact inner_sub_le_one_of_subset hω0 hω1 hcos hK harea hS ht1 ht2 hp hq

end Sofa
