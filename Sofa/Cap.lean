/-
# Sofa/Cap.lean — caps and niches (Baek §2.4)

* `IsCap K ω` (Def 2.4.1), `niche K ω` (Def 2.4.5; the fan `F_ω` is `fan ω` from Basic.lean);
* **Thm 2.4.1** `C(S)` is a cap; **Thm 2.4.2** `I(S) = C(S) \ N(C(S))`;
  **Thm 2.4.3** (monotone sofas); **Thm 2.4.4** (`I(I(S)) = I(S)`).

Condition 2 of Def 2.4.1 ("K is an intersection of closed half-planes with normal angles in
`J_ω ∪ {ω + π, 3π/2}`") is formalised in the equivalent form "K is the intersection of its own
supporting half-planes with those normal angles" (`IsCap.eq_iInter`).

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 1 (2026-09-17, Opus 5), no `sorry`.
-/
import Sofa.MonoSofa

noncomputable section

open Real Set MovingSofa
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa

variable {S K : Set ℝ²} {ω : ℝ}

/-- The admissible normal angles of a cap: `J_ω ∪ {ω + π, 3π/2}`. -/
def capAngles (ω : ℝ) : Set ℝ := Jω ω ∪ {ω + π, 3 * π / 2}

/-- **Def 2.4.1.** A cap with rotation angle `ω`. -/
structure IsCap (K : Set ℝ²) (ω : ℝ) : Prop where
  convex : Convex ℝ K
  isCompact : IsCompact K
  nonempty : K.Nonempty
  supportFn_ω : supportFn K ω = 1
  supportFn_pi_div_two : supportFn K (π / 2) = 1
  supportFn_ω_add_pi : supportFn K (ω + π) = 0
  supportFn_three_pi_div_two : supportFn K (3 * π / 2) = 0
  eq_iInter : K = ⋂ t ∈ capAngles ω, hpLe t (supportFn K t)

/-- **Def 2.4.5.** The niche `N(K) = F_ω ∩ ⋃_{t ∈ (0, ω)} Q⁻_K(t)`. -/
def niche (K : Set ℝ²) (ω : ℝ) : Set ℝ² := fan ω ∩ ⋃ t ∈ Ioo (0 : ℝ) ω, QminusS K t

lemma mem_niche_iff {p : ℝ²} :
    p ∈ niche K ω ↔ p ∈ fan ω ∧ ∃ t ∈ Ioo (0 : ℝ) ω, p ∈ QminusS K t := by
  simp only [niche, mem_inter_iff, mem_iUnion₂, exists_prop]

lemma para_subset_fan (ω : ℝ) : para ω ⊆ fan ω := fun _ hp => ⟨hp.1.1, hp.2.1⟩

lemma mem_para_iff {p : ℝ²} :
    p ∈ para ω ↔ (0 ≤ p 1 ∧ p 1 ≤ 1) ∧ (0 ≤ ⟪p, u ω⟫ ∧ ⟪p, u ω⟫ ≤ 1) := Iff.rfl

/-! ## Directions in which `Q⁺_S(t)` is closed -/

lemma closedDir_QplusS {t : ℝ} {w : ℝ²} (h1 : ⟪w, u t⟫ ≤ 0) (h2 : ⟪w, v t⟫ ≤ 0) :
    ClosedDir (QplusS S t) w := by
  intro x hx r hr
  rw [mem_QplusS_iff] at hx ⊢
  rw [u_add_pi_div_two] at hx ⊢
  rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  constructor
  · nlinarith [mul_nonneg hr (neg_nonneg.2 h1)]
  · nlinarith [mul_nonneg hr (neg_nonneg.2 h2)]

lemma add_mem_Ccap {w : ℝ²} (hw : ∀ t ∈ Icc (0 : ℝ) ω, ⟪w, u t⟫ ≤ 0 ∧ ⟪w, v t⟫ ≤ 0)
    {p : ℝ²} (hp : ∀ t ∈ Icc (0 : ℝ) ω, p ∈ QplusS S t) (hP : p + w ∈ para ω) :
    p + w ∈ Ccap S ω := by
  refine mem_Ccap_iff.2 ⟨hP, fun t ht => ?_⟩
  have := closedDir_QplusS (S := S) (hw t ht).1 (hw t ht).2 p (hp t ht) 1 zero_le_one
  rwa [one_smul] at this

/-- For `t ∈ [0, ω] ⊆ [0, π/2]`, `Q⁺_S(t)` is closed in the direction `-v₀ = (0, -1)`. -/
lemma dir_neg_v_zero (hω1 : ω ≤ π / 2) :
    ∀ t ∈ Icc (0 : ℝ) ω, ⟪-v 0, u t⟫ ≤ 0 ∧ ⟪-v 0, v t⟫ ≤ 0 := by
  intro t ht
  rw [inner_neg_left, inner_neg_left, inner_eq, inner_eq]
  simp only [v_coord_zero, v_coord_one, u_coord_zero, u_coord_one, sin_zero, cos_zero]
  have hs := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [pi_pos, ht.2] : t ≤ π)
  have hc := cos_nonneg_of_mem_Icc
    (⟨by linarith [pi_pos, ht.1], by linarith [ht.2]⟩ : t ∈ Icc (-(π / 2)) (π / 2))
  constructor <;> nlinarith

/-- For `t ∈ [0, ω] ⊆ [0, π/2]`, `Q⁺_S(t)` is closed in the direction `-u_ω`. -/
lemma dir_neg_u (hω1 : ω ≤ π / 2) :
    ∀ t ∈ Icc (0 : ℝ) ω, ⟪-u ω, u t⟫ ≤ 0 ∧ ⟪-u ω, v t⟫ ≤ 0 := by
  intro t ht
  rw [inner_neg_left, inner_neg_left, inner_u_u_eq_cos, inner_u_v_eq_sin, neg_nonpos,
    neg_nonpos]
  exact ⟨cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos, ht.2], by linarith [ht.1]⟩,
    sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.2]) (by linarith [pi_pos, ht.1])⟩

/-! ## Theorem 2.4.1 -/

/-- The upper right vertex `o_ω = ((1 - sin ω)/cos ω, 1)` of `P_ω` lies in every `Q⁺_S(t)`
(proof of Thm 2.4.1, case `ω < π/2`). -/
lemma oω_mem_QplusS (h : IsSofaWithAngle S ω) (hstd : StdPos S ω) (hω0 : 0 < ω)
    (hlt : ω < π / 2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ω) :
    pt ((1 - sin ω) / cos ω) 1 ∈ QplusS S t := by
  have hS := h.isCompact
  have hne := h.nonempty
  have hSP := (h.subset hstd).1
  have hc : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith, hlt⟩
  have hxo : (1 - sin ω) / cos ω * cos ω = 1 - sin ω := by field_simp
  obtain ⟨qω, hqω, hqω1⟩ := exists_supportFn_eq hS hne ω
  obtain ⟨qπ, hqπ, hqπ1⟩ := exists_supportFn_eq hS hne (π / 2)
  rw [hstd.1, inner_eq, u_coord_zero, u_coord_one] at hqω1
  rw [hstd.2, inner_u_pi_div_two] at hqπ1
  have hqωy : qω 1 ≤ 1 := (hSP hqω).1.2
  have hqπx : qπ 0 * cos ω + qπ 1 * sin ω ≤ 1 := by
    have := (hSP hqπ).2.2
    rwa [inner_eq, u_coord_zero, u_coord_one] at this
  have hqπx' : qπ 0 ≤ (1 - sin ω) / cos ω := by
    rw [← mul_le_mul_iff_of_pos_right hc, hxo]
    rw [hqπ1] at hqπx
    linarith
  have hst : 0 ≤ sin t := sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [pi_pos, ht.2])
  have hsin : 0 ≤ sin ω * cos t - cos ω * sin t := by
    rw [← sin_sub]
    exact sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.2]) (by linarith [pi_pos, ht.1])
  rw [mem_QplusS_iff, u_add_pi_div_two]
  constructor
  · refine le_trans ?_ (le_supportFn hS hqω t)
    rw [inner_eq, inner_eq, pt_zero, pt_one, u_coord_zero, u_coord_one]
    have key : (qω 0 - (1 - sin ω) / cos ω) * cos ω = (1 - qω 1) * sin ω := by
      rw [sub_mul, hxo]; linarith
    have hD : ((qω 0 - (1 - sin ω) / cos ω) * cos t + (qω 1 - 1) * sin t) * cos ω
        = (1 - qω 1) * (sin ω * cos t - cos ω * sin t) := by
      linear_combination cos t * key
    have hD0 : 0 ≤ (qω 0 - (1 - sin ω) / cos ω) * cos t + (qω 1 - 1) * sin t := by
      by_contra hneg
      push Not at hneg
      have h1 := mul_neg_of_neg_of_pos hneg hc
      have h2 := mul_nonneg (sub_nonneg.2 hqωy) hsin
      linarith
    linarith
  · have := le_supportFn hS hqπ (t + π / 2)
    rw [u_add_pi_div_two] at this
    refine le_trans ?_ this
    rw [inner_eq, inner_eq, pt_zero, pt_one, v_coord_zero, v_coord_one, hqπ1]
    nlinarith [mul_le_mul_of_nonneg_right hqπx' hst]

/-- `C(S)` meets the lower sides `y = 0` and `⟪p, u_ω⟫ = 0` of `P_ω`. -/
lemma exists_low_points (h : IsSofaWithAngle S ω) (hstd : StdPos S ω) (hω0 : 0 < ω)
    (hω1 : ω ≤ π / 2) :
    (∃ z ∈ Ccap S ω, z 1 = 0) ∧ (∃ z ∈ Ccap S ω, ⟪z, u ω⟫ = 0) := by
  have hS := h.isCompact
  have hne := h.nonempty
  have hsub : S ⊆ Ccap S ω := (h.subset_Imono hstd).trans (Imono_subset_Ccap S ω)
  rcases hω1.lt_or_eq with hlt | heq
  · have hc : 0 < cos ω := cos_pos_of_mem_Ioo ⟨by linarith, hlt⟩
    have hs : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
    have hs1 : sin ω ≤ 1 := sin_le_one ω
    have hxo : (1 - sin ω) / cos ω * cos ω = 1 - sin ω := by field_simp
    have hoQ := fun t (ht : t ∈ Icc (0 : ℝ) ω) => oω_mem_QplusS h hstd hω0 hlt ht
    have hcs := sin_sq_add_cos_sq ω
    have e1 : pt ((1 - sin ω) / cos ω) 1 + -v 0 = pt ((1 - sin ω) / cos ω) 0 := by
      ext i; fin_cases i <;> simp [pt, e₀, e₁, v]
    have e2 : pt ((1 - sin ω) / cos ω) 1 + -u ω = pt ((1 - sin ω) / cos ω - cos ω) (1 - sin ω) := by
      ext i; fin_cases i <;> simp [pt, e₀, e₁, u] <;> ring
    have hz1 := add_mem_Ccap (dir_neg_v_zero hω1) hoQ (by
      rw [e1, mem_para_iff, inner_eq, pt_zero, pt_one, u_coord_zero, u_coord_one, hxo]
      constructor <;> constructor <;> linarith)
    have hz2 := add_mem_Ccap (dir_neg_u hω1) hoQ (by
      rw [e2, mem_para_iff, inner_eq, pt_zero, pt_one, u_coord_zero, u_coord_one, sub_mul, hxo]
      constructor <;> constructor <;> nlinarith)
    refine ⟨⟨_, hz1, by rw [e1, pt_one]⟩, ⟨_, hz2, ?_⟩⟩
    rw [e2, inner_eq, pt_zero, pt_one, u_coord_zero, u_coord_one, sub_mul, hxo]
    nlinarith
  · subst heq
    obtain ⟨qπ, hqπ, hqπ1⟩ := exists_supportFn_eq hS hne (π / 2)
    rw [hstd.2, inner_u_pi_div_two] at hqπ1
    have hqQ := (mem_Ccap_iff.1 (hsub hqπ)).2
    have hz : qπ + -v 0 ∈ Ccap S (π / 2) := by
      refine add_mem_Ccap (dir_neg_v_zero le_rfl) hqQ ?_
      rw [mem_para_iff, inner_u_pi_div_two]
      simp only [PiLp.add_apply, PiLp.neg_apply, hqπ1, v_coord_one, cos_zero]
      norm_num
    have hz1 : (qπ + -v 0) 1 = 0 := by simp [hqπ1, v]
    exact ⟨⟨_, hz, hz1⟩, ⟨_, hz, by rw [inner_u_pi_div_two, hz1]⟩⟩

lemma u_three_pi_div_two : u (3 * π / 2) = -u (π / 2) := by
  rw [show 3 * π / 2 = π / 2 + π by ring, u_add_pi]

/-- **Theorem 2.4.1.** `C(S)` is a cap with rotation angle `ω`. -/
theorem IsSofaWithAngle.isCap_Ccap (h : IsSofaWithAngle S ω) (hstd : StdPos S ω)
    (hω0 : 0 < ω) (hω1 : ω ≤ π / 2) : IsCap (Ccap S ω) ω := by
  have hne := h.nonempty
  have hsub : S ⊆ Ccap S ω := (h.subset_Imono hstd).trans (Imono_subset_Ccap S ω)
  have hC := isCompact_Ccap (S := S) hω0 hω1
  have hCne : (Ccap S ω).Nonempty := hne.mono hsub
  have hJ : ∀ t ∈ Jω ω, supportFn (Ccap S ω) t = supportFn S t := fun t ht =>
    supportFn_eq_of_subset_Ccap hC hne hsub subset_rfl ht
  have hωJ : ω ∈ Jω ω := Or.inl ⟨hω0.le, le_rfl⟩
  have hπJ : π / 2 ∈ Jω ω := Or.inr ⟨le_rfl, by linarith⟩
  -- the two lower support values
  have hup1 : supportFn (Ccap S ω) (ω + π) ≤ 0 := by
    rw [supportFn_le_iff hC hCne]
    intro p hp
    rw [u_add_pi, inner_neg_right, neg_nonpos]
    exact hp.1.2.1
  have hup2 : supportFn (Ccap S ω) (3 * π / 2) ≤ 0 := by
    rw [supportFn_le_iff hC hCne]
    intro p hp
    rw [u_three_pi_div_two, inner_neg_right, neg_nonpos, inner_u_pi_div_two]
    exact hp.1.1.1
  obtain ⟨⟨z1, hz1, hz1'⟩, ⟨z2, hz2, hz2'⟩⟩ := exists_low_points h hstd hω0 hω1
  have hlow1 : 0 ≤ supportFn (Ccap S ω) (ω + π) := by
    refine le_trans (le_of_eq ?_) (le_supportFn hC hz2 _)
    rw [u_add_pi, inner_neg_right, hz2', neg_zero]
  have hlow2 : 0 ≤ supportFn (Ccap S ω) (3 * π / 2) := by
    refine le_trans (le_of_eq ?_) (le_supportFn hC hz1 _)
    rw [u_three_pi_div_two, inner_neg_right, inner_u_pi_div_two, hz1', neg_zero]
  refine ⟨convex_Ccap S ω, hC, hCne, by rw [hJ ω hωJ, hstd.1], by rw [hJ _ hπJ, hstd.2],
    le_antisymm hup1 hlow1, le_antisymm hup2 hlow2, ?_⟩
  -- condition 2
  apply Subset.antisymm
  · exact subset_iInter₂ fun t _ => subset_hpLe_supportFn hC t
  · intro p hp
    rw [mem_iInter₂] at hp
    have hω' := hp ω (Or.inl hωJ)
    have hπ' := hp (π / 2) (Or.inl hπJ)
    have hωπ := hp (ω + π) (Or.inr (Or.inl rfl))
    have h3π := hp (3 * π / 2) (Or.inr (Or.inr rfl))
    simp only [hpLe, mem_ofPred_eq] at hω' hπ' hωπ h3π
    rw [hJ ω hωJ, hstd.1] at hω'
    rw [hJ _ hπJ, hstd.2, inner_u_pi_div_two] at hπ'
    rw [le_antisymm hup1 hlow1, u_add_pi, inner_neg_right, neg_nonpos] at hωπ
    rw [le_antisymm hup2 hlow2, u_three_pi_div_two, inner_neg_right, neg_nonpos,
      inner_u_pi_div_two] at h3π
    refine mem_Ccap_iff.2 ⟨⟨⟨h3π, hπ'⟩, hωπ, hω'⟩, fun t ht => ?_⟩
    have ht1 := hp t (Or.inl (mem_Jω_of_mem_Icc ht))
    have ht2 := hp (t + π / 2) (Or.inl (add_pi_div_two_mem_Jω ht))
    simp only [hpLe, mem_ofPred_eq] at ht1 ht2
    rw [hJ t (mem_Jω_of_mem_Icc ht)] at ht1
    rw [hJ _ (add_pi_div_two_mem_Jω ht)] at ht2
    exact ⟨ht1, ht2⟩

/-! ## Theorems 2.4.2 – 2.4.4 -/

/-- **Theorem 2.4.2.** `I(S) = K \ N(K)` for the cap `K = C(S)`. -/
theorem IsSofaWithAngle.Imono_eq_Ccap_sdiff (h : IsSofaWithAngle S ω) (hstd : StdPos S ω) (hω0 : 0 < ω)
    (hω1 : ω ≤ π / 2) : Imono S ω = Ccap S ω \ niche (Ccap S ω) ω := by
  have hne := h.nonempty
  have hsub : S ⊆ Ccap S ω := (h.subset_Imono hstd).trans (Imono_subset_Ccap S ω)
  have hC := isCompact_Ccap (S := S) hω0 hω1
  have hJ : ∀ t ∈ Jω ω, supportFn (Ccap S ω) t = supportFn S t := fun t ht =>
    supportFn_eq_of_subset_Ccap hC hne hsub subset_rfl ht
  have hQ : ∀ t ∈ Icc (0 : ℝ) ω, QminusS (Ccap S ω) t = QminusS S t := fun t ht =>
    QminusS_congr (hJ t (mem_Jω_of_mem_Icc ht)) (hJ _ (add_pi_div_two_mem_Jω ht))
  ext p
  simp only [mem_sdiff, mem_Imono_iff, mem_Ccap_iff, mem_niche_iff, suppHallway_eq]
  constructor
  · rintro ⟨hP, hL⟩
    refine ⟨⟨hP, fun t ht => (hL t ht).1⟩, ?_⟩
    rintro ⟨-, t, ht, hpt⟩
    rw [hQ t (Ioo_subset_Icc_self ht)] at hpt
    exact (hL t (Ioo_subset_Icc_self ht)).2 hpt
  · rintro ⟨⟨hP, hQp⟩, hN⟩
    refine ⟨hP, fun t ht => ⟨hQp t ht, fun hpt => ?_⟩⟩
    rcases ht.1.lt_or_eq with ht0 | ht0
    · rcases ht.2.lt_or_eq with ht1 | ht1
      · refine hN ⟨para_subset_fan ω hP, t, ⟨ht0, ht1⟩, ?_⟩
        rw [hQ t ht]; exact hpt
      · -- `t = ω`: `Q⁻_S(ω)` misses `V_ω`
        subst ht1
        have := hpt.1
        simp only [hpLt, mem_ofPred_eq, hstd.1, sub_self] at this
        exact absurd hP.2.1 (not_le.2 this)
    · -- `t = 0`: `Q⁻_S(0)` misses `H`
      subst ht0
      have := hpt.2
      simp only [hpLt, mem_ofPred_eq, zero_add, hstd.2, sub_self, inner_u_pi_div_two] at this
      exact absurd hP.1.1 (not_le.2 this)

/-- `C(I(S)) = C(S)` and `I(I(S)) = I(S)`: both only depend on the support function on `J_ω`. -/
lemma IsSofaWithAngle.supportFn_Imono (h : IsSofaWithAngle S ω) (hstd : StdPos S ω)
    (hω0 : 0 < ω) (hω1 : ω ≤ π / 2) {t : ℝ} (ht : t ∈ Jω ω) :
    supportFn (Imono S ω) t = supportFn S t :=
  supportFn_eq_of_subset_Ccap (isCompact_Imono hω0 hω1) h.nonempty (h.subset_Imono hstd)
    (Imono_subset_Ccap S ω) ht

/-- **Theorem 2.4.4.** `I(I(S)) = I(S)`. -/
theorem IsSofaWithAngle.Imono_Imono (h : IsSofaWithAngle S ω) (hstd : StdPos S ω)
    (hω0 : 0 < ω) (hω1 : ω ≤ π / 2) : Imono (Imono S ω) ω = Imono S ω :=
  Imono_congr fun _ ht => h.supportFn_Imono hstd hω0 hω1 ht

/-- **Theorem 2.4.3.** A monotone sofa is its cap minus the niche of its cap. -/
theorem IsMonotoneSofa.eq_Ccap_sdiff_niche {T : Set ℝ²} (hT : IsMonotoneSofa T ω)
    (hω0 : 0 < ω) (hω1 : ω ≤ π / 2) : T = Ccap T ω \ niche (Ccap T ω) ω := by
  obtain ⟨S, hS, hstd, rfl⟩ := hT
  have hCC : Ccap (Imono S ω) ω = Ccap S ω :=
    Ccap_congr fun _ ht => hS.supportFn_Imono hstd hω0 hω1 ht
  rw [hCC]
  exact hS.Imono_eq_Ccap_sdiff hstd hω0 hω1

/-- **Theorem 2.4.4 (second part).** A moving sofa `S` in standard position satisfies
`S = I(S)` iff it is monotone. -/
theorem IsSofaWithAngle.eq_Imono_iff (h : IsSofaWithAngle S ω) (hstd : StdPos S ω)
    (hω0 : 0 < ω) (hω1 : ω ≤ π / 2) : S = Imono S ω ↔ IsMonotoneSofa S ω := by
  constructor
  · intro hS
    exact ⟨S, h, hstd, hS⟩
  · intro hT
    obtain ⟨S', hS', hstd', rfl⟩ := hT
    have hS'' : IsSofaWithAngle S' ω := hS'
    exact (hS''.Imono_Imono hstd' hω0 hω1).symm

end Sofa
