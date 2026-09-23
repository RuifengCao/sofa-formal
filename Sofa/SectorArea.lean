/-
# Sofa/SectorArea.lean — towards Baek Theorem 7.1.3 (`|K| = ½ ∫ h_K dσ_K`)

Step 4 of the route described in `blueprint/ch3-8.md` §15.4: on a short interval of normal
angles the cross product of the two vertices is `h_K(b) · σ_K((a,b])` up to `O(δ σ)`:

    `|v⁺_K(a) × v⁺_K(b) − σ_K((a,b]) h_K(b)| ≤ 2 (b−a) σ_K((a,b]) (2R + σ_K((a,b]))`

for `0 ≤ b − a ≤ 1` and `‖·‖ ≤ R` on `K`.  This is exactly the two-sided estimate of
`Sofa/SurfaceArea.lean` (`0 ≤ ⟪d, u_b⟫ ≤ tan δ σ`, `0 ≤ σ − ⟪d, v_b⟫ ≤ δ tan δ σ`) fed through
the frame decomposition `d = ⟪d,u_b⟫ u_b + ⟪d,v_b⟫ v_b` and `A × u_b = −⟪A, v_b⟫`,
`A × v_b = ⟪A, u_b⟫`.

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.ArmLength
import Sofa.Triangle

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²}

/-- `A × B = −⟪B − A, u_b⟫ ⟪A, v_b⟫ + ⟪B − A, v_b⟫ ⟪A, u_b⟫`. -/
lemma cross_eq_frame (A B : ℝ²) (b : ℝ) :
    cross A B = -(⟪B - A, u b⟫ * ⟪A, v b⟫) + ⟪B - A, v b⟫ * ⟪A, u b⟫ := by
  have hd : B - A = ⟪B - A, u b⟫ • u b + ⟪B - A, v b⟫ • v b := decomp_u_v b _
  have h1 : cross A B = cross A (B - A) := by
    have : B = A + (B - A) := by abel
    rw [this, cross_add_right, cross_self, zero_add]
    congr 1
    abel
  rw [h1]
  conv_lhs => rw [hd]
  rw [cross_add_right, cross_smul_right, cross_smul_right, cross_u, cross_v]
  ring

/-- The scalar estimate behind Step 4. -/
lemma abs_frame_bound {p q sr x y δ R : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 2 * δ * sr)
    (hq : sr - q ≤ 2 * δ * δ * sr) (hq0 : q ≤ sr) (hsr : 0 ≤ sr) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |-(p * y) + q * x - sr * (x + p)| ≤ 2 * δ * sr * (2 * R + sr) := by
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) hx
  have h1 : |p * y| ≤ 2 * δ * sr * R := by
    rw [abs_mul, abs_of_nonneg hp0]
    exact mul_le_mul hp hy (abs_nonneg _) (by positivity)
  have h2 : |(q - sr) * x| ≤ 2 * δ * sr * R := by
    rw [abs_mul]
    refine mul_le_mul ?_ hx (abs_nonneg _) (by positivity)
    rw [abs_of_nonpos (by linarith), neg_sub]
    nlinarith
  have h3 : |sr * p| ≤ sr * (2 * δ * sr) := by
    rw [abs_mul, abs_of_nonneg hsr, abs_of_nonneg hp0]
    exact mul_le_mul_of_nonneg_left hp hsr
  have ht : |(-(p * y) + (q - sr) * x - sr * p)| ≤ |p * y| + |(q - sr) * x| + |sr * p| := by
    have e1 := abs_add_le (-(p * y) + (q - sr) * x) (-(sr * p))
    have e2 := abs_add_le (-(p * y)) ((q - sr) * x)
    rw [abs_neg] at e1 e2
    rw [show -(p * y) + (q - sr) * x - sr * p = -(p * y) + (q - sr) * x + -(sr * p) by ring]
    linarith
  have heq : -(p * y) + q * x - sr * (x + p) = -(p * y) + (q - sr) * x - sr * p := by ring
  rw [heq]
  nlinarith [ht, h1, h2, h3]

/-- **Step 4 for Thm 7.1.3**: `v⁺_K(a) × v⁺_K(b) ≈ σ_K((a,b]) · h_K(b)`. -/
theorem abs_cross_vtxP_sub_le (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ} (hab : a ≤ b)
    (hδ : b - a ≤ 1) {R : ℝ} (hR : ∀ p ∈ K, ‖p‖ ≤ R) :
    |cross (vtxP K a) (vtxP K b) - (arcFn K b - arcFn K a) * supportFn K b|
      ≤ 2 * (b - a) * (arcFn K b - arcFn K a) * (2 * R + (arcFn K b - arcFn K a)) := by
  have hpi := pi_gt_three
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = b - a := ⟨_, rfl⟩
  obtain ⟨sr, hsrdef⟩ : ∃ s : ℝ, s = arcFn K b - arcFn K a := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδdef]; linarith
  have hδ1 : δ ≤ 1 := by rw [hδdef]; linarith
  have hδπ : b - a < π / 2 := by linarith
  have hsr0 : 0 ≤ sr := by rw [hsrdef]; linarith [arcFn_mono hK hne hab]
  have htan0 : 0 ≤ tan δ := tan_nonneg_of_nonneg_of_le_pi_div_two hδ0 (by linarith)
  have htan : tan δ ≤ 2 * δ := tan_le_two_mul hδ0 hδ1
  -- the two-sided bounds from `Sofa/SurfaceArea.lean`
  have hu0 : 0 ≤ ⟪vtxP K b - vtxP K a, u b⟫ := inner_vtxP_sub_u_nonneg hK hne a b
  have hv0 : 0 ≤ ⟪vtxP K b - vtxP K a, v b⟫ := inner_vtxP_sub_v_nonneg hK hne hab hδπ
  have hvle : ⟪vtxP K b - vtxP K a, v b⟫ ≤ sr := by
    rw [hsrdef]; exact inner_vtxP_sub_v_le_arcFn hK hne hab
  have hule : ⟪vtxP K b - vtxP K a, u b⟫ ≤ tan δ * sr := by
    have h1 := inner_vtxP_sub_u_le_tan hK hne hab hδπ
    rw [← hδdef] at h1
    nlinarith
  have hvge : sr - ⟪vtxP K b - vtxP K a, v b⟫ ≤ δ * (tan δ * sr) := by
    have h := arcFn_sub_le hK hne hab hδπ
    rw [← hδdef, ← hsrdef] at h
    exact h
  -- the support function at `b`
  have hsupp : supportFn K b = ⟪vtxP K a, u b⟫ + ⟪vtxP K b - vtxP K a, u b⟫ := by
    rw [inner_sub_left, inner_vtxP_u]; ring
  -- bounds on the coordinates of `v⁺_K(a)`
  have hnormA : ‖vtxP K a‖ ≤ R := hR _ (vtxP_mem hK hne a)
  have hAu : |⟪vtxP K a, u b⟫| ≤ R := by
    refine le_trans ?_ hnormA
    have h := abs_real_inner_le_norm (vtxP K a) (u b)
    rwa [norm_u, mul_one] at h
  have hAv : |⟪vtxP K a, v b⟫| ≤ R := by
    refine le_trans ?_ hnormA
    have h := abs_real_inner_le_norm (vtxP K a) (v b)
    rwa [norm_v, mul_one] at h
  have hR0 : 0 ≤ R := le_trans (abs_nonneg _) hAu
  -- combine
  rw [cross_eq_frame _ _ b, ← hsrdef, hsupp, ← hδdef]
  refine abs_frame_bound hu0 ?_ ?_ hvle hsr0 hδ0 hδ1 hAu hAv
  · nlinarith
  · have h1 : tan δ * sr ≤ 2 * δ * sr := mul_le_mul_of_nonneg_right htan hsr0
    have h2 : δ * (tan δ * sr) ≤ δ * (2 * δ * sr) := mul_le_mul_of_nonneg_left h1 hδ0
    linarith [hvge]

/-! ## Step 3: the sector is squeezed between two triangles

The upper bound avoids the chord–arc "cap" geometry entirely: writing `q ∈ sector K A B` as
`q = sA + tB` with `s, t ≥ 0` (Cramer), the single supporting constraint `⟪q, u_b⟫ ≤ h_K(b)`
already forces `s + t ≤ β/(β − p)` with `β = h_K(b)` and `p = ⟪B − A, u_b⟫`.  Hence the sector is
inside the *scaled* triangle, whose area is `(β/(β−p))²` times that of `tri A B`. -/

/-- Cramer's decomposition of a point of a (nondegenerate) wedge. -/
lemma mem_wedgeC_decomp {A B q : ℝ²} (hAB : 0 < cross A B) (hq : q ∈ wedgeC A B) :
    ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ q = s • A + t • B := by
  have hne : cross A B ≠ 0 := ne_of_gt hAB
  refine ⟨cross q B / cross A B, cross A q / cross A B, ?_, ?_, ?_⟩
  · refine div_nonneg ?_ hAB.le
    have := hq.2
    rw [cross_comm B q] at this
    linarith
  · exact div_nonneg hq.1 hAB.le
  · have h := cross_cramer A q B
    have hq' : (cross A B)⁻¹ • (cross A B • q) = q := by
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    calc q = (cross A B)⁻¹ • (cross A B • q) := hq'.symm
      _ = (cross A B)⁻¹ • (cross q B • A + cross A q • B) := by rw [h]
      _ = (cross q B / cross A B) • A + (cross A q / cross A B) • B := by
          rw [smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]

/-- **Step 3 (upper bound).**  The sector lies inside the triangle scaled by `β/(β − p)`. -/
theorem sector_subset_tri_smul {K : Set ℝ²} {A B : ℝ²} {β p t : ℝ}
    (hsub : ∀ q ∈ K, ⟪q, u t⟫ ≤ β) (hB : ⟪B, u t⟫ = β) (hA : ⟪A, u t⟫ = β - p)
    (hβ : 0 < β) (hp0 : 0 ≤ p) (hpβ : p < β) (hAB : 0 < cross A B) :
    sector K A B ⊆ tri ((β / (β - p)) • A) ((β / (β - p)) • B) := by
  obtain ⟨lam, hlam⟩ : ∃ l : ℝ, l = β / (β - p) := ⟨_, rfl⟩
  have hβp : 0 < β - p := by linarith
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  rintro q ⟨hqK, hw⟩
  obtain ⟨s, r, hs, hr, rfl⟩ := mem_wedgeC_decomp hAB hw
  -- the single supporting constraint
  have hcon : s * (β - p) + r * β ≤ β := by
    have h := hsub _ hqK
    rwa [inner_add_left, real_inner_smul_left, real_inner_smul_left, hA, hB] at h
  have hsum : s + r ≤ lam := by
    rw [hlam, le_div_iff₀ hβp]
    nlinarith
  refine mem_tri.2 ⟨s / lam, r / lam, by positivity, by positivity, ?_, ?_⟩
  · rw [← add_div, div_le_one hlam0]; exact hsum
  · rw [smul_smul, smul_smul, ← hlam, div_mul_cancel₀ _ (ne_of_gt hlam0),
      div_mul_cancel₀ _ (ne_of_gt hlam0)]

lemma cross_smul_smul (c : ℝ) (A B : ℝ²) : cross (c • A) (c • B) = c ^ 2 * cross A B := by
  rw [cross_smul_left, cross_smul_right]; ring

/-- **Step 3 (both bounds).** -/
theorem volume_sector_squeeze {K : Set ℝ²} (hconv : Convex ℝ K) (h0 : (0:ℝ²) ∈ K)
    {A B : ℝ²} (hAK : A ∈ K) (hBK : B ∈ K) {β p t : ℝ}
    (hsub : ∀ q ∈ K, ⟪q, u t⟫ ≤ β) (hB : ⟪B, u t⟫ = β) (hA : ⟪A, u t⟫ = β - p)
    (hβ : 0 < β) (hp0 : 0 ≤ p) (hpβ : p < β) (hAB : 0 < cross A B) :
    ENNReal.ofReal (cross A B / 2) ≤ volume (sector K A B) ∧
      volume (sector K A B) ≤ ENNReal.ofReal ((β / (β - p)) ^ 2 * cross A B / 2) := by
  constructor
  · have hsub1 : tri A B ⊆ sector K A B := fun q hq =>
      ⟨tri_subset_of_convex hconv h0 hAK hBK hq, tri_subset_wedgeC hAB.le hq⟩
    have := measure_mono (μ := volume) hsub1
    rwa [volume_tri, abs_of_nonneg hAB.le] at this
  · have h := measure_mono (μ := volume) (sector_subset_tri_smul hsub hB hA hβ hp0 hpβ hAB)
    rw [volume_tri, cross_smul_smul, abs_of_nonneg (by positivity)] at h
    exact h

/-! ## Step 5(a): nondegeneracy of the sector

`A_a × A_b ≥ q (h_K(b) − p) − p R` with `p = ⟪A_b − A_a, u_b⟫ ∈ [0, tan δ q]` and
`q = ⟪A_b − A_a, v_b⟫ ∈ [0, σ_K((a,b])]`, so the wedge is nondegenerate as soon as
`tan δ (R + σ) ≤ h_min`. -/

/-- If the surface measure of `(a,b]` vanishes then the two vertices coincide. -/
theorem vtxP_eq_of_arcFn_eq (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ} (hab : a ≤ b)
    (hδ : b - a < π / 2) (h : arcFn K a = arcFn K b) : vtxP K a = vtxP K b := by
  have hq0 : 0 ≤ ⟪vtxP K b - vtxP K a, v b⟫ := inner_vtxP_sub_v_nonneg hK hne hab hδ
  have hqle : ⟪vtxP K b - vtxP K a, v b⟫ ≤ 0 := by
    have := inner_vtxP_sub_v_le_arcFn hK hne hab
    linarith
  have hq : ⟪vtxP K b - vtxP K a, v b⟫ = 0 := le_antisymm hqle hq0
  have hp0 : 0 ≤ ⟪vtxP K b - vtxP K a, u b⟫ := inner_vtxP_sub_u_nonneg hK hne a b
  have hple : ⟪vtxP K b - vtxP K a, u b⟫ ≤ 0 := by
    have h1 := inner_vtxP_sub_u_le_tan hK hne hab hδ
    rw [hq, mul_zero] at h1
    exact h1
  have hp : ⟪vtxP K b - vtxP K a, u b⟫ = 0 := le_antisymm hple hp0
  have hd : vtxP K b - vtxP K a = 0 := by
    have := decomp_u_v b (vtxP K b - vtxP K a)
    rw [hp, hq, zero_smul, zero_smul, add_zero] at this
    exact this
  exact (sub_eq_zero.1 hd).symm

/-- **Step 5(a)**: the wedge spanned by `v⁺_K(a)`, `v⁺_K(b)` is positively oriented. -/
theorem cross_vtxP_nonneg (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ} (hab : a ≤ b)
    (hδ : b - a < π / 2) {R hm : ℝ} (hR : ∀ p ∈ K, ‖p‖ ≤ R) (_hm0 : 0 < hm)
    (hmin : hm ≤ supportFn K b)
    (hsmall : tan (b - a) * (R + (arcFn K b - arcFn K a)) ≤ hm) :
    0 ≤ cross (vtxP K a) (vtxP K b) := by
  have htan0 : 0 ≤ tan (b - a) :=
    tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith)
  have hp0 : 0 ≤ ⟪vtxP K b - vtxP K a, u b⟫ := inner_vtxP_sub_u_nonneg hK hne a b
  have hq0 : 0 ≤ ⟪vtxP K b - vtxP K a, v b⟫ := inner_vtxP_sub_v_nonneg hK hne hab hδ
  have hqle : ⟪vtxP K b - vtxP K a, v b⟫ ≤ arcFn K b - arcFn K a :=
    inner_vtxP_sub_v_le_arcFn hK hne hab
  have hple : ⟪vtxP K b - vtxP K a, u b⟫ ≤ tan (b - a) * ⟪vtxP K b - vtxP K a, v b⟫ :=
    inner_vtxP_sub_u_le_tan hK hne hab hδ
  have hAu : ⟪vtxP K a, u b⟫ = supportFn K b - ⟪vtxP K b - vtxP K a, u b⟫ := by
    rw [inner_sub_left, inner_vtxP_u]; ring
  have hnormA : ‖vtxP K a‖ ≤ R := hR _ (vtxP_mem hK hne a)
  have hAv : ⟪vtxP K a, v b⟫ ≤ R := by
    refine le_trans ?_ hnormA
    have h := real_inner_le_norm (vtxP K a) (v b)
    rwa [norm_v, mul_one] at h
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) hnormA
  have t1 : ⟪vtxP K b - vtxP K a, u b⟫ * ⟪vtxP K a, v b⟫
      ≤ ⟪vtxP K b - vtxP K a, u b⟫ * R := mul_le_mul_of_nonneg_left hAv hp0
  have t2 : ⟪vtxP K b - vtxP K a, u b⟫ * R
      ≤ (tan (b - a) * ⟪vtxP K b - vtxP K a, v b⟫) * R := mul_le_mul_of_nonneg_right hple hR0
  have t4 : tan (b - a) * ⟪vtxP K b - vtxP K a, v b⟫
      ≤ tan (b - a) * (arcFn K b - arcFn K a) := mul_le_mul_of_nonneg_left hqle htan0
  have t3 : ⟪vtxP K b - vtxP K a, v b⟫ * ⟪vtxP K b - vtxP K a, u b⟫
      ≤ ⟪vtxP K b - vtxP K a, v b⟫ * (tan (b - a) * ⟪vtxP K b - vtxP K a, v b⟫) :=
    mul_le_mul_of_nonneg_left hple hq0
  have t3' : ⟪vtxP K b - vtxP K a, v b⟫ * (tan (b - a) * ⟪vtxP K b - vtxP K a, v b⟫)
      ≤ ⟪vtxP K b - vtxP K a, v b⟫ * (tan (b - a) * (arcFn K b - arcFn K a)) :=
    mul_le_mul_of_nonneg_left t4 hq0
  have t5 : (tan (b - a) * (R + (arcFn K b - arcFn K a))) * ⟪vtxP K b - vtxP K a, v b⟫
      ≤ hm * ⟪vtxP K b - vtxP K a, v b⟫ := mul_le_mul_of_nonneg_right hsmall hq0
  have t6 : ⟪vtxP K b - vtxP K a, v b⟫ * hm
      ≤ ⟪vtxP K b - vtxP K a, v b⟫ * supportFn K b := mul_le_mul_of_nonneg_left hmin hq0
  rw [cross_eq_frame _ _ b, hAu]
  nlinarith [t1, t2, t3, t3', t5, t6]

end Sofa
