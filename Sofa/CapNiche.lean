/-
# Sofa/CapNiche.lean — the cap contains the niche (Baek §2.5, part 1)

* structure of caps: `K ⊆ P_ω`, the corner points `A = (h_K(0), 0)`, `C = h_K(ω+π/2) v_ω`
  (Baek's `A⁻_K(0)` and `C⁺_K(ω)`), and the "bottom boundary" lemma;
* `W_K(t)`, `Z_K(t)` (Def 2.5.4), the gaps `w_K(t)`, `z_K(t)` (Def 2.5.5) and
  **Thm 2.5.5** (`w_K(t), z_K(t) > 0`);
* the wedge `T_K(t)` (Def 2.5.3), Prop 2.5.3, **Lemma 2.5.6** (`x_K(t) ∈ K ⇒ T_K(t) ⊆ K`, by a
  uniform "sweep" argument instead of Baek's four cases), **Lemma 2.5.7**.

Remark: for caps the vertices `A⁻_K(0)`, `C⁺_K(ω)` have the closed forms above, so the general
vertex machinery (Def 2.1.10, Thm 2.1.3) is not needed here.

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 1 (2026-09-17, Opus 5): compiled in the cloud dev tree
(Lean 4.33.1, Mathlib v4.33.1 with subset imports), no `sorry`; full `import Mathlib` re-check pending.
-/
import Sofa.Cap

noncomputable section

open Real Set MovingSofa
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa

variable {K : Set ℝ²} {ω : ℝ}

lemma convex_lerp_mem {K : Set ℝ²} (hK : Convex ℝ K) {x y : ℝ²} (hx : x ∈ K) (hy : y ∈ K)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : (1 - r) • x + r • y ∈ K :=
  hK hx hy (by linarith) hr0 (by ring)

lemma coord_one_eq_inner (p : ℝ²) : p 1 = ⟪p, u (π / 2)⟫ := (inner_u_pi_div_two p).symm

namespace IsCap

variable (hK : IsCap K ω)
include hK

lemma mem_iff {p : ℝ²} : p ∈ K ↔ ∀ t ∈ capAngles ω, ⟪p, u t⟫ ≤ supportFn K t := by
  conv_lhs => rw [hK.eq_iInter]
  simp only [mem_iInter₂, hpLe, mem_ofPred_eq]

lemma inner_le {p : ℝ²} (hp : p ∈ K) (t : ℝ) : ⟪p, u t⟫ ≤ supportFn K t :=
  le_supportFn hK.isCompact hp t

lemma subset_para : K ⊆ para ω := by
  intro p hp
  have h1 := hK.inner_le hp ω
  have h2 := hK.inner_le hp (π / 2)
  have h3 := hK.inner_le hp (ω + π)
  have h4 := hK.inner_le hp (3 * π / 2)
  rw [hK.supportFn_ω] at h1
  rw [hK.supportFn_pi_div_two, inner_u_pi_div_two] at h2
  rw [hK.supportFn_ω_add_pi, u_add_pi, inner_neg_right, neg_nonpos] at h3
  rw [hK.supportFn_three_pi_div_two, u_three_pi_div_two, inner_neg_right, neg_nonpos,
    inner_u_pi_div_two] at h4
  exact ⟨⟨h4, h2⟩, h3, h1⟩

lemma subset_fan : K ⊆ fan ω := hK.subset_para.trans (para_subset_fan ω)

/-- A point of `K` on the bottom line `y = 0`. -/
lemma exists_bottom : ∃ B ∈ K, B 1 = 0 := by
  obtain ⟨B, hB, hB1⟩ := exists_supportFn_eq hK.isCompact hK.nonempty (3 * π / 2)
  refine ⟨B, hB, ?_⟩
  rw [hK.supportFn_three_pi_div_two, u_three_pi_div_two, inner_neg_right,
    inner_u_pi_div_two, neg_eq_zero] at hB1
  exact hB1

/-- A point of `K` on the lower-left line `⟪p, u_ω⟫ = 0`. -/
lemma exists_bottom' : ∃ B ∈ K, ⟪B, u ω⟫ = 0 := by
  obtain ⟨B, hB, hB1⟩ := exists_supportFn_eq hK.isCompact hK.nonempty (ω + π)
  refine ⟨B, hB, ?_⟩
  rw [hK.supportFn_ω_add_pi, u_add_pi, inner_neg_right, neg_eq_zero] at hB1
  exact hB1

/-- The lower right corner `A = (h_K(0), 0)` (= Baek's `A⁻_K(0)`). -/
def cornerA (_ : IsCap K ω) : ℝ² := supportFn K 0 • u 0

/-- The lower left corner `C = h_K(ω+π/2) v_ω` (= Baek's `C⁺_K(ω)`). -/
def cornerC (_ : IsCap K ω) : ℝ² := supportFn K (ω + π / 2) • v ω

lemma cornerA_eq : hK.cornerA = pt (supportFn K 0) 0 := by
  ext i; fin_cases i <;> simp [cornerA, pt, u, e₀, e₁]

lemma cornerC_eq : hK.cornerC =
    pt (-(supportFn K (ω + π / 2) * sin ω)) (supportFn K (ω + π / 2) * cos ω) := by
  ext i; fin_cases i <;> simp [cornerC, pt, v, e₀, e₁]

variable (hω0 : 0 < ω) (hω1 : ω ≤ π / 2)
include hω0 hω1

lemma cornerA_mem : hK.cornerA ∈ K := by
  rw [hK.mem_iff]
  obtain ⟨B, hB, hB1⟩ := hK.exists_bottom
  obtain ⟨R, hR, hR1⟩ := exists_supportFn_eq hK.isCompact hK.nonempty 0
  rw [inner_u_zero] at hR1
  have hRy : 0 ≤ R 1 := (hK.subset_para hR).1.1
  have hBx : B 0 ≤ supportFn K 0 := by have := hK.inner_le hB 0; rwa [inner_u_zero] at this
  have hBF := (hK.subset_para hB).2.1
  simp only [inner_eq, hB1, u_coord_zero, u_coord_one, zero_mul, add_zero] at hBF
  have hc : 0 ≤ cos ω := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hω1⟩
  rw [hK.cornerA_eq]
  rintro s ((⟨hs0, hs1⟩ | ⟨hs0, hs1⟩) | hs | hs)
  · -- `⟪A, u_s⟫ ≤ ⟪R, u_s⟫`
    refine le_trans ?_ (hK.inner_le hR s)
    have hss := sin_nonneg_of_nonneg_of_le_pi hs0 (by linarith [pi_pos])
    simp only [inner_eq, pt_zero, pt_one, u_coord_zero, u_coord_one, hR1]
    nlinarith [mul_nonneg hRy hss]
  · -- `⟪A, u_s⟫ ≤ ⟪B, u_s⟫`
    refine le_trans ?_ (hK.inner_le hB s)
    have hcs : cos s ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le hs0 (by linarith [pi_pos])
    simp only [inner_eq, pt_zero, pt_one, u_coord_zero, u_coord_one, hB1]
    nlinarith [mul_le_mul_of_nonpos_right hBx hcs]
  · rw [hs, hK.supportFn_ω_add_pi]
    simp only [inner_eq, pt_zero, pt_one, u_coord_zero, u_coord_one, cos_add_pi, zero_mul,
      add_zero]
    nlinarith [mul_le_mul_of_nonneg_right hBx hc]
  · rw [mem_singleton_iff] at hs
    rw [hs, hK.supportFn_three_pi_div_two, u_three_pi_div_two]
    simp [inner_eq, u]

lemma cornerC_mem : hK.cornerC ∈ K := by
  rw [hK.mem_iff]
  obtain ⟨B, hB, hB1⟩ := hK.exists_bottom'
  obtain ⟨R, hR, hR1⟩ := exists_supportFn_eq hK.isCompact hK.nonempty (ω + π / 2)
  rw [u_add_pi_div_two] at hR1
  have hRu : 0 ≤ ⟪R, u ω⟫ := (hK.subset_para hR).2.1
  have hBv : ⟪B, v ω⟫ ≤ supportFn K (ω + π / 2) := by
    have := hK.inner_le hB (ω + π / 2); rwa [u_add_pi_div_two] at this
  have hBy : 0 ≤ B 1 := (hK.subset_para hB).1.1
  have hc : 0 ≤ cos ω := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hω1⟩
  -- coordinates of `B` and `R` in the frame `(u_ω, v_ω)`
  have hcs := sin_sq_add_cos_sq ω
  set β := ⟪B, v ω⟫ with hβ
  set h' := supportFn K (ω + π / 2) with hh'
  set ρ := ⟪R, u ω⟫ with hρ
  have hB0 : B 0 = -(β * sin ω) := by
    have e1 := hB1
    simp only [inner_eq, u_coord_zero, u_coord_one] at e1
    simp only [hβ, inner_eq, v_coord_zero, v_coord_one]
    linear_combination (cos ω) * e1 - (B 0) * hcs
  have hB1' : B 1 = β * cos ω := by
    have e1 := hB1
    simp only [inner_eq, u_coord_zero, u_coord_one] at e1
    simp only [hβ, inner_eq, v_coord_zero, v_coord_one]
    linear_combination (sin ω) * e1 - (B 1) * hcs
  have hR0 : R 0 = ρ * cos ω - h' * sin ω := by
    have e1 := hR1
    simp only [inner_eq, v_coord_zero, v_coord_one] at e1
    simp only [hρ, inner_eq, u_coord_zero, u_coord_one]
    linear_combination (-sin ω) * e1 - (R 0) * hcs
  have hR1' : R 1 = ρ * sin ω + h' * cos ω := by
    have e1 := hR1
    simp only [inner_eq, v_coord_zero, v_coord_one] at e1
    simp only [hρ, inner_eq, u_coord_zero, u_coord_one]
    linear_combination (cos ω) * e1 - (R 1) * hcs
  rw [hK.cornerC_eq]
  rintro s ((⟨hs0, hs1⟩ | ⟨hs0, hs1⟩) | hs | hs)
  · -- `⟪C, u_s⟫ ≤ ⟪B, u_s⟫`
    refine le_trans ?_ (hK.inner_le hB s)
    have hsn : sin (s - ω) ≤ 0 :=
      sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [pi_pos])
    rw [sin_sub] at hsn
    simp only [inner_eq, pt_zero, pt_one, u_coord_zero, u_coord_one, hB0, hB1']
    nlinarith [mul_le_mul_of_nonpos_right hBv hsn]
  · -- `⟪C, u_s⟫ ≤ ⟪R, u_s⟫`
    refine le_trans ?_ (hK.inner_le hR s)
    have hcs' : 0 ≤ cos (s - ω) :=
      cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith⟩
    rw [cos_sub] at hcs'
    simp only [inner_eq, pt_zero, pt_one, u_coord_zero, u_coord_one, hR0, hR1']
    nlinarith [mul_nonneg hRu hcs']
  · rw [hs, hK.supportFn_ω_add_pi]
    simp only [inner_eq, pt_zero, pt_one, u_coord_zero, u_coord_one, cos_add_pi, sin_add_pi]
    nlinarith
  · rw [mem_singleton_iff] at hs
    rw [hs, hK.supportFn_three_pi_div_two, u_three_pi_div_two]
    simp only [inner_eq, pt_zero, pt_one, PiLp.neg_apply, u_coord_zero, u_coord_one,
      cos_pi_div_two, sin_pi_div_two]
    have hβ0 : 0 ≤ β * cos ω := by rw [← hB1']; exact hBy
    have : 0 ≤ h' * cos ω := by
      rcases hc.lt_or_eq with hc' | hc'
      · have h0 : 0 ≤ β := nonneg_of_mul_nonneg_left hβ0 hc'
        exact mul_nonneg (h0.trans hBv) hc
      · rw [← hc', mul_zero]
    nlinarith

end IsCap

/-! ## Trigonometric helpers for `0 < t < ω ≤ π/2` -/

lemma trig_facts {t : ℝ} (ht : t ∈ Ioo 0 ω) (hω1 : ω ≤ π / 2) :
    0 < sin t ∧ 0 < cos t ∧ sin t < 1 ∧ 0 < sin (ω - t) ∧ 0 < cos (ω - t) ∧ sin (ω - t) < 1 := by
  obtain ⟨h0, h1⟩ := ht
  refine ⟨sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos]),
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩, ?_,
    sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos]),
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩, ?_⟩
  · have := sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [pi_pos]) le_rfl (by linarith :
      t < π / 2)
    rwa [sin_pi_div_two] at this
  · have := sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [pi_pos]) le_rfl (by linarith :
      ω - t < π / 2)
    rwa [sin_pi_div_two] at this

/-- `⟪q, v_t⟫ = ⟪q, u_ω⟫ sin (ω - t) + ⟪q, v_ω⟫ cos (ω - t)`. -/
lemma inner_v_decomp (q : ℝ²) (ω t : ℝ) :
    ⟪q, v t⟫ = ⟪q, u ω⟫ * sin (ω - t) + ⟪q, v ω⟫ * cos (ω - t) := by
  simp only [inner_eq, u_coord_zero, u_coord_one, v_coord_zero, v_coord_one, sin_sub, cos_sub]
  linear_combination (q 0 * sin t - q 1 * cos t) * sin_sq_add_cos_sq ω

lemma inner_innerCorner_v {S : Set ℝ²} (t : ℝ) :
    ⟪innerCorner S t, v t⟫ = supportFn S (t + π / 2) - 1 := by
  rw [innerCorner, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_v,
    inner_v_v]; ring

/-- A segment lemma: if `a • w, b • w ∈ K` and `a ≤ x ≤ b` then `x • w ∈ K`. -/
lemma smul_mem_of_le_of_le {K : Set ℝ²} (hK : Convex ℝ K) {w : ℝ²} {a b x : ℝ}
    (ha : a • w ∈ K) (hb : b • w ∈ K) (hax : a ≤ x) (hxb : x ≤ b) : x • w ∈ K := by
  rcases hax.lt_or_eq with h | h
  · have hlt : a < b := lt_of_lt_of_le h hxb
    have hr0 : 0 ≤ (x - a) / (b - a) := div_nonneg (by linarith) (by linarith)
    have hr1 : (x - a) / (b - a) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    have hmem := convex_lerp_mem hK ha hb hr0 hr1
    have hba : b - a ≠ 0 := (sub_pos.2 hlt).ne'
    convert hmem using 1
    rw [smul_smul, smul_smul, ← add_smul]
    congr 1
    field_simp
    ring
  · rw [← h]; exact ha

/-! ## `W_K(t)`, `Z_K(t)` and the gaps (Def 2.5.4, 2.5.5) -/

/-- `W_K(t) = b_K(t) ∩ l(π/2, 0) = ((h_K(t) - 1)/cos t, 0)`. -/
def wedgeW (K : Set ℝ²) (t : ℝ) : ℝ² := ((supportFn K t - 1) / cos t) • u 0

/-- `Z_K(t) = d_K(t) ∩ l(ω, 0) = ((h_K(t+π/2) - 1)/cos (ω-t)) v_ω`. -/
def wedgeZ (K : Set ℝ²) (ω t : ℝ) : ℝ² :=
  ((supportFn K (t + π / 2) - 1) / cos (ω - t)) • v ω

/-- The right wedge gap `w_K(t) = (A⁻_K(0) - W_K(t)) · u₀`. -/
def gapW (K : Set ℝ²) (t : ℝ) : ℝ := supportFn K 0 - (supportFn K t - 1) / cos t

/-- The left wedge gap `z_K(t) = (C⁺_K(ω) - Z_K(t)) · v_ω`. -/
def gapZ (K : Set ℝ²) (ω t : ℝ) : ℝ :=
  supportFn K (ω + π / 2) - (supportFn K (t + π / 2) - 1) / cos (ω - t)

/-- The wedge `T_K(t) = F_ω ∩ Q⁻_K(t)` (Def 2.5.3). -/
def wedge (K : Set ℝ²) (ω t : ℝ) : Set ℝ² := fan ω ∩ QminusS K t

/-- **Prop 2.5.3.** -/
lemma niche_eq_iUnion_wedge (K : Set ℝ²) (ω : ℝ) :
    niche K ω = ⋃ t ∈ Ioo (0 : ℝ) ω, wedge K ω t := by
  ext p
  simp only [niche, wedge, mem_inter_iff, mem_iUnion₂, exists_prop]
  constructor
  · rintro ⟨hF, t, ht, hq⟩; exact ⟨t, ht, hF, hq⟩
  · rintro ⟨t, ht, hF, hq⟩; exact ⟨hF, t, ht, hq⟩

namespace IsCap

variable (hK : IsCap K ω) (hω0 : 0 < ω) (hω1 : ω ≤ π / 2)
include hK hω0 hω1

omit hω0 in
/-- **Theorem 2.5.5 (right gap).** -/
theorem gapW_pos {t : ℝ} (ht : t ∈ Ioo 0 ω) : 0 < gapW K t := by
  obtain ⟨hst, hct, hst1, -, -, -⟩ := trig_facts ht hω1
  obtain ⟨e, he, he1⟩ := exists_supportFn_eq hK.isCompact hK.nonempty t
  have hey : e 1 ≤ 1 := (hK.subset_para he).1.2
  have hex : e 0 ≤ supportFn K 0 := by have := hK.inner_le he 0; rwa [inner_u_zero] at this
  rw [inner_u_decomp] at he1
  rw [gapW, sub_pos, div_lt_iff₀ hct]
  nlinarith [mul_le_mul_of_nonneg_right hex hct.le, mul_le_mul_of_nonneg_right hey hst.le]

omit hω0 in
/-- **Theorem 2.5.5 (left gap).** -/
theorem gapZ_pos {t : ℝ} (ht : t ∈ Ioo 0 ω) : 0 < gapZ K ω t := by
  obtain ⟨-, -, -, hs, hc, hs1⟩ := trig_facts ht hω1
  obtain ⟨e, he, he1⟩ := exists_supportFn_eq hK.isCompact hK.nonempty (t + π / 2)
  rw [u_add_pi_div_two, inner_v_decomp e ω t] at he1
  have heu : ⟪e, u ω⟫ ≤ 1 := (hK.subset_para he).2.2
  have hev : ⟪e, v ω⟫ ≤ supportFn K (ω + π / 2) := by
    have := hK.inner_le he (ω + π / 2); rwa [u_add_pi_div_two] at this
  rw [gapZ, sub_pos, div_lt_iff₀ hc]
  nlinarith [mul_le_mul_of_nonneg_right hev hc.le, mul_le_mul_of_nonneg_right heu hs.le]

omit hω1 in
lemma supportFn_zero_nonneg (hlt : ω < π / 2) : 0 ≤ supportFn K 0 := by
  obtain ⟨B, hB, hB1⟩ := hK.exists_bottom
  have hBF := (hK.subset_para hB).2.1
  rw [inner_u_decomp, hB1, zero_mul, add_zero] at hBF
  have hc : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hlt⟩
  have h0 : 0 ≤ B 0 := nonneg_of_mul_nonneg_left hBF hc
  have := hK.inner_le hB 0
  rw [inner_u_zero] at this
  linarith

omit hω1 in
lemma supportFn_left_nonneg (hlt : ω < π / 2) : 0 ≤ supportFn K (ω + π / 2) := by
  obtain ⟨B, hB, hB1⟩ := hK.exists_bottom'
  have hBy : 0 ≤ B 1 := (hK.subset_para hB).1.1
  have hc : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hlt⟩
  have hBv : ⟪B, v ω⟫ * cos ω = B 1 := by
    simp only [inner_eq, v_coord_zero, v_coord_one]
    have e1 := hB1
    rw [inner_u_decomp] at e1
    linear_combination (-sin ω) * e1 + (B 1) * sin_sq_add_cos_sq ω
  have h0 : 0 ≤ ⟪B, v ω⟫ := nonneg_of_mul_nonneg_left (hBv ▸ hBy) hc
  have := hK.inner_le hB (ω + π / 2)
  rw [u_add_pi_div_two] at this
  linarith

/-- For `ω < π/2` the lower left vertex `O` of `P_ω` lies in every cap. -/
lemma zero_mem (hlt : ω < π / 2) : (0 : ℝ²) ∈ K := by
  have hA := hK.cornerA_mem hω0 hω1
  have hC := hK.cornerC_mem hω0 hω1
  have hA0 := hK.supportFn_zero_nonneg hω0 hlt
  have hC0 := hK.supportFn_left_nonneg hω0 hlt
  rw [hK.mem_iff]
  rintro s ((⟨hs0, hs1⟩ | ⟨hs0, hs1⟩) | hs | hs)
  · refine le_trans ?_ (hK.inner_le hA s)
    rw [inner_zero_left, cornerA, real_inner_smul_left, inner_u_u_eq_cos, zero_sub, cos_neg]
    exact mul_nonneg hA0 (cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith⟩)
  · refine le_trans ?_ (hK.inner_le hC s)
    rw [inner_zero_left, cornerC, real_inner_smul_left, inner_v_u_eq_sin]
    exact mul_nonneg hC0 (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos]))
  · rw [hs, hK.supportFn_ω_add_pi, inner_zero_left]
  · rw [mem_singleton_iff] at hs
    rw [hs, hK.supportFn_three_pi_div_two, inner_zero_left]

/-- **The bottom boundary lemma.**  A point of the fan lying on one of its two boundary rays
and below the corners `A`, `C` belongs to the cap. -/
lemma mem_of_bottom {q : ℝ²} (hqF : q ∈ fan ω) (hq : q 1 = 0 ∨ ⟪q, u ω⟫ = 0)
    (hqA : q 0 ≤ supportFn K 0) (hqC : ⟪q, v ω⟫ ≤ supportFn K (ω + π / 2)) : q ∈ K := by
  have hA := hK.cornerA_mem hω0 hω1
  have hC := hK.cornerC_mem hω0 hω1
  rcases hω1.lt_or_eq with hlt | heq
  · have hO := hK.zero_mem hω0 hω1 hlt
    have hc : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hlt⟩
    rcases hq with hq | hq
    · -- on the bottom ray
      have hqe : q = q 0 • u 0 := by
        ext i; fin_cases i <;> simp [u, hq]
      have hq0 : 0 ≤ q 0 := by
        have := hqF.2
        rw [inner_u_decomp, hq, zero_mul, add_zero] at this
        exact nonneg_of_mul_nonneg_left this hc
      rw [hqe]
      exact smul_mem_of_le_of_le hK.convex (by rwa [zero_smul]) hA hq0 hqA
    · -- on the left ray
      have hqe : q = ⟪q, v ω⟫ • v ω := by
        have := decomp_u_v ω q
        rwa [hq, zero_smul, zero_add] at this
      have hq1 : 0 ≤ ⟪q, v ω⟫ := by
        have h1 := hqF.1
        rw [hqe] at h1
        simp only [PiLp.smul_apply, v_coord_one, smul_eq_mul] at h1
        exact nonneg_of_mul_nonneg_left h1 hc
      rw [hqe]
      exact smul_mem_of_le_of_le hK.convex (by rwa [zero_smul]) hC hq1 hqC
  · -- `ω = π/2`: the whole bottom line
    subst heq
    have hq1 : q 1 = 0 := by
      rcases hq with hq | hq
      · exact hq
      · rwa [inner_u_pi_div_two] at hq
    have hqe : q = q 0 • u 0 := by
      ext i; fin_cases i <;> simp [u, hq1]
    have hCe : hK.cornerC = (-supportFn K (π / 2 + π / 2)) • u 0 := by
      ext i; fin_cases i <;> simp [cornerC, u, v]
    have hqC' : -supportFn K (π / 2 + π / 2) ≤ q 0 := by
      have : ⟪q, v (π / 2)⟫ = -q 0 := by simp [inner_eq, v]
      linarith
    rw [hqe]
    exact smul_mem_of_le_of_le hK.convex (hCe ▸ hC) hA hqC' hqA

end IsCap

lemma eq_of_inner_u_v_eq {p q : ℝ²} {t : ℝ} (h1 : ⟪p, u t⟫ = ⟪q, u t⟫)
    (h2 : ⟪p, v t⟫ = ⟪q, v t⟫) : p = q := by
  rw [decomp_u_v t p, decomp_u_v t q, h1, h2]

namespace IsCap

variable (hK : IsCap K ω) (hω0 : 0 < ω) (hω1 : ω ≤ π / 2)
include hK hω0 hω1

/-- **Lemma 2.5.6.** If the inner corner `x_K(t)` lies in `K`, then so does the wedge `T_K(t)`.

Proof (uniform in the position of `O`): for `p ∈ T_K(t)` move along `u_t` up to the inner wall
`b_K(t)` (point `p₁`, which lies between `x_K(t)` and the exit point `E` of `b_K(t)` from the fan)
and down to the boundary of the fan (point `p₃`); `E` and `p₃` lie on the bottom boundary below
the corners, hence in `K`, and `p ∈ [p₃, p₁]`. -/
theorem wedge_subset {t : ℝ} (ht : t ∈ Ioo 0 ω) (hx : innerCorner K t ∈ K) :
    wedge K ω t ⊆ K := by
  obtain ⟨hst, hct, -, hsw, hcw, -⟩ := trig_facts ht hω1
  have hW := hK.gapW_pos hω1 ht
  have hZ := hK.gapZ_pos hω1 ht
  rw [gapW] at hW
  rw [gapZ] at hZ
  have hct' := hct.ne'
  have hst' := hst.ne'
  have hcw' := hcw.ne'
  have hsw' := hsw.ne'
  obtain ⟨a, ha⟩ : ∃ a, a = supportFn K t - 1 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = supportFn K (t + π / 2) - 1 := ⟨_, rfl⟩
  obtain ⟨x, hxd⟩ : ∃ x, x = innerCorner K t := ⟨_, rfl⟩
  rw [← hxd] at hx
  have hxu : ⟪x, u t⟫ = a := by rw [hxd, ha]; exact inner_innerCorner_u t
  have hxv : ⟪x, v t⟫ = b := by rw [hxd, hb]; exact inner_innerCorner_v t
  have hxF : x ∈ fan ω := hK.subset_fan hx
  rw [← ha] at hW
  rw [← hb] at hZ
  -- bounds for points of the closed wedge
  have boundA : ∀ q ∈ fan ω, ⟪q, u t⟫ ≤ a → q 0 ≤ supportFn K 0 := by
    intro q hqF hq
    rw [inner_u_decomp] at hq
    have hq0 : q 0 * cos t ≤ a := by nlinarith [mul_nonneg hqF.1 hst.le]
    have : q 0 ≤ a / cos t := by rw [le_div_iff₀ hct]; exact hq0
    linarith
  have boundC : ∀ q ∈ fan ω, ⟪q, v t⟫ ≤ b → ⟪q, v ω⟫ ≤ supportFn K (ω + π / 2) := by
    intro q hqF hq
    rw [inner_v_decomp q ω t] at hq
    have hq0 : ⟪q, v ω⟫ * cos (ω - t) ≤ b := by nlinarith [mul_nonneg hqF.2 hsw.le]
    have : ⟪q, v ω⟫ ≤ b / cos (ω - t) := by rw [le_div_iff₀ hcw]; exact hq0
    linarith
  -- moving along `u_t` and `v_t`
  have mv1 : ∀ (q : ℝ²) (r : ℝ), (q + r • u t) 1 = q 1 + r * sin t := by intro q r; simp [u]
  have mv2 : ∀ (q : ℝ²) (r : ℝ), ⟪q + r • u t, u ω⟫ = ⟪q, u ω⟫ + r * cos (ω - t) := by
    intro q r
    rw [inner_add_left, real_inner_smul_left, inner_u_u_eq_cos, ← cos_neg, neg_sub]
  have mv3 : ∀ (q : ℝ²) (r : ℝ), (q + r • v t) 1 = q 1 + r * cos t := by intro q r; simp [v]
  have mv4 : ∀ (q : ℝ²) (r : ℝ), ⟪q + r • v t, u ω⟫ = ⟪q, u ω⟫ + r * sin (ω - t) := by
    intro q r; rw [inner_add_left, real_inner_smul_left, inner_v_u_eq_sin]
  have mvu : ∀ (q : ℝ²) (r : ℝ), ⟪q + r • u t, u t⟫ = ⟪q, u t⟫ + r := by
    intro q r; rw [inner_add_left, real_inner_smul_left, inner_u_u, mul_one]
  have mvv : ∀ (q : ℝ²) (r : ℝ), ⟪q + r • u t, v t⟫ = ⟪q, v t⟫ := by
    intro q r; rw [inner_add_left, real_inner_smul_left, inner_u_v, mul_zero, add_zero]
  have mwu : ∀ (q : ℝ²) (r : ℝ), ⟪q + r • v t, u t⟫ = ⟪q, u t⟫ := by
    intro q r; rw [inner_add_left, real_inner_smul_left, inner_v_u, mul_zero, add_zero]
  have mwv : ∀ (q : ℝ²) (r : ℝ), ⟪q + r • v t, v t⟫ = ⟪q, v t⟫ + r := by
    intro q r; rw [inner_add_left, real_inner_smul_left, inner_v_v, mul_one]
  rintro p ⟨hpF, hpQ⟩
  rw [mem_QminusS_iff, u_add_pi_div_two, ← ha, ← hb] at hpQ
  obtain ⟨hpa, hpb⟩ := hpQ
  -- Step 1: `p₁ = p + λ u_t` on the inner wall `b_K(t)`
  obtain ⟨lam, hlam⟩ : ∃ l, l = a - ⟪p, u t⟫ := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; linarith
  obtain ⟨p₁, hp₁⟩ : ∃ q, q = p + lam • u t := ⟨_, rfl⟩
  have hp₁F : p₁ ∈ fan ω := by
    rw [hp₁]
    exact ⟨by rw [mv1]; nlinarith [hpF.1, mul_pos hlam0 hst],
      by rw [mv2]; nlinarith [hpF.2, mul_pos hlam0 hcw]⟩
  have hp₁u : ⟪p₁, u t⟫ = a := by rw [hp₁, mvu, hlam]; ring
  have hp₁v : ⟪p₁, v t⟫ < b := by rw [hp₁, mvv]; exact hpb
  obtain ⟨κ, hκ⟩ : ∃ k, k = b - ⟪p₁, v t⟫ := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  have hp₁x : p₁ = x + (-κ) • v t := by
    refine eq_of_inner_u_v_eq (t := t) ?_ ?_
    · rw [mwu, hp₁u, hxu]
    · rw [mwv, hxv, hκ]; ring
  -- the exit point `E = x - ν v_t` of the inner wall from the fan
  obtain ⟨ν, hν⟩ : ∃ n, n = min (x 1 / cos t) (⟪x, u ω⟫ / sin (ω - t)) := ⟨_, rfl⟩
  have hκν : κ ≤ ν := by
    have h1 : 0 ≤ p₁ 1 := hp₁F.1
    have h2 : 0 ≤ ⟪p₁, u ω⟫ := hp₁F.2
    rw [hp₁x, mv3] at h1
    rw [hp₁x, mv4] at h2
    rw [hν]
    apply le_min
    · rw [le_div_iff₀ hct]; linarith
    · rw [le_div_iff₀ hsw]; linarith
  have hν0 : 0 < ν := lt_of_lt_of_le hκ0 hκν
  obtain ⟨E, hE⟩ : ∃ e, e = x + (-ν) • v t := ⟨_, rfl⟩
  have hν1 : ν ≤ x 1 / cos t := hν ▸ min_le_left _ _
  have hν2 : ν ≤ ⟪x, u ω⟫ / sin (ω - t) := hν ▸ min_le_right _ _
  rw [le_div_iff₀ hct] at hν1
  rw [le_div_iff₀ hsw] at hν2
  have hEF : E ∈ fan ω := by
    rw [hE]
    exact ⟨by rw [mv3]; linarith, by rw [mv4]; linarith⟩
  have hEbot : E 1 = 0 ∨ ⟪E, u ω⟫ = 0 := by
    rcases min_choice (x 1 / cos t) (⟪x, u ω⟫ / sin (ω - t)) with h | h
    · left
      rw [← hν] at h
      rw [hE, mv3, h]
      field_simp
      ring
    · right
      rw [← hν] at h
      rw [hE, mv4, h]
      field_simp
      ring
  have hEu : ⟪E, u t⟫ = a := by rw [hE, mwu, hxu]
  have hEv : ⟪E, v t⟫ ≤ b := by rw [hE, mwv, hxv]; linarith
  have hEK : E ∈ K := hK.mem_of_bottom hω0 hω1 hEF hEbot (boundA E hEF hEu.le) (boundC E hEF hEv)
  have hp₁K : p₁ ∈ K := by
    have hmem := convex_lerp_mem hK.convex hx hEK (r := κ / ν) (div_nonneg hκ0.le hν0.le)
      ((div_le_one hν0).2 hκν)
    have hcoef : κ / ν * (-ν) = -κ := by field_simp
    have e : (1 - κ / ν) • x + (κ / ν) • (x + (-ν) • v t) = x + (κ / ν * (-ν)) • v t := by
      module
    rw [hE, e, hcoef, ← hp₁x] at hmem
    exact hmem
  -- Step 2: `p₃ = p - μ u_t` on the boundary of the fan
  obtain ⟨μ, hμ⟩ : ∃ m, m = min (p 1 / sin t) (⟪p, u ω⟫ / cos (ω - t)) := ⟨_, rfl⟩
  have hμ0 : 0 ≤ μ := by
    rw [hμ]; exact le_min (div_nonneg hpF.1 hst.le) (div_nonneg hpF.2 hcw.le)
  have hμ1 : μ ≤ p 1 / sin t := hμ ▸ min_le_left _ _
  have hμ2 : μ ≤ ⟪p, u ω⟫ / cos (ω - t) := hμ ▸ min_le_right _ _
  rw [le_div_iff₀ hst] at hμ1
  rw [le_div_iff₀ hcw] at hμ2
  obtain ⟨p₃, hp₃⟩ : ∃ q, q = p + (-μ) • u t := ⟨_, rfl⟩
  have hp₃F : p₃ ∈ fan ω := by
    rw [hp₃]
    exact ⟨by rw [mv1]; linarith, by rw [mv2]; linarith⟩
  have hp₃bot : p₃ 1 = 0 ∨ ⟪p₃, u ω⟫ = 0 := by
    rcases min_choice (p 1 / sin t) (⟪p, u ω⟫ / cos (ω - t)) with h | h
    · left
      rw [← hμ] at h
      rw [hp₃, mv1, h]
      field_simp
      ring
    · right
      rw [← hμ] at h
      rw [hp₃, mv2, h]
      field_simp
      ring
  have hp₃u : ⟪p₃, u t⟫ ≤ a := by rw [hp₃, mvu]; linarith
  have hp₃v : ⟪p₃, v t⟫ ≤ b := by rw [hp₃, mvv]; exact hpb.le
  have hp₃K : p₃ ∈ K :=
    hK.mem_of_bottom hω0 hω1 hp₃F hp₃bot (boundA p₃ hp₃F hp₃u) (boundC p₃ hp₃F hp₃v)
  -- Step 3: `p ∈ [p₃, p₁]`
  have hsum : 0 < μ + lam := by linarith
  have hmem := convex_lerp_mem hK.convex hp₃K hp₁K (r := μ / (μ + lam))
    (div_nonneg hμ0 hsum.le) ((div_le_one hsum).2 (by linarith))
  have hsum' := hsum.ne'
  have e : (1 - μ / (μ + lam)) • (p + (-μ) • u t) + (μ / (μ + lam)) • (p + lam • u t)
      = p + ((1 - μ / (μ + lam)) * (-μ) + μ / (μ + lam) * lam) • u t := by
    module
  have hcoef : (1 - μ / (μ + lam)) * (-μ) + μ / (μ + lam) * lam = 0 := by
    field_simp
    ring
  rw [hp₃, hp₁, e, hcoef, zero_smul, add_zero] at hmem
  exact hmem

omit hω0 in
/-- **Lemma 2.5.7** (right corner). -/
theorem cornerA_not_mem_niche : hK.cornerA ∉ niche K ω := by
  rw [niche_eq_iUnion_wedge]
  simp only [mem_iUnion₂, not_exists]
  rintro t ht ⟨-, hQ⟩
  rw [mem_QminusS_iff] at hQ
  have hW := hK.gapW_pos hω1 ht
  obtain ⟨-, hct, -⟩ := trig_facts ht hω1
  rw [gapW, sub_pos, div_lt_iff₀ hct] at hW
  have := hQ.1
  rw [cornerA, real_inner_smul_left, inner_u_u_eq_cos, zero_sub, cos_neg] at this
  linarith

omit hω0 in
/-- **Lemma 2.5.7** (left corner). -/
theorem cornerC_not_mem_niche : hK.cornerC ∉ niche K ω := by
  rw [niche_eq_iUnion_wedge]
  simp only [mem_iUnion₂, not_exists]
  rintro t ht ⟨-, hQ⟩
  rw [mem_QminusS_iff] at hQ
  have hZ := hK.gapZ_pos hω1 ht
  obtain ⟨-, -, -, -, hcw, -⟩ := trig_facts ht hω1
  rw [gapZ, sub_pos, div_lt_iff₀ hcw] at hZ
  have := hQ.2
  rw [cornerC, u_add_pi_div_two, real_inner_smul_left, inner_v_v_eq_cos, ← cos_neg,
    neg_sub] at this
  linarith

end IsCap

end Sofa
