/-
# Sofa/HammersleySofa.lean — Hammersley's sofa; the lower bound `π/2 + 2/π ≤ sofaConstant`
(milestone M-H)

Why this is on the critical path: Baek's Thm 1.5.1 only treats moving sofas of area `≥ 2.2`.
To conclude `sofaConstant ≤ |G|` one needs *some* moving sofa of area `> 2.2` (then the main
theorem applied to it gives `|G| > 2.2`, and sofas of area `< 2.2` are trivially fine).
Hammersley's sofa (area `π/2 + 2/π ≈ 2.2074`) is the cheapest witness; the alternative would be
a numerical evaluation of `|G|`.  By-product: upstream's `one_le_sofaConstant` is improved.

The sofa `hsofa r` (hole radius `r`, placed so that its rightmost point is `(1, 0)`):
  quarter disc `x ≥ 0, x² + y² ≤ 1`  ∪  rectangle `[-2r, 0] × [0, 1]`
  ∪  quarter disc `x ≤ -2r, (x + 2r)² + y² ≤ 1`,  minus the open half disc `(x + r)² + y² < r²`.
The motion `hmotion r`: at time `τ` rotate clockwise by `t = πτ/2` about the moving inner corner
`x(t) = 2r sin t · v_t`, which runs along the semicircle bounding the hole.

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 1 (2026-09-17, Opus 5): compiled in the cloud dev tree
(Lean 4.33.1, Mathlib v4.33.1 with subset imports), no `sorry`; full `import Mathlib` re-check pending.
-/
import Sofa.Motion
import Sofa.Support

noncomputable section

open Real Set MovingSofa MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace unitInterval ENNReal

namespace Sofa

section HSofa

variable (r : ℝ)

/-- Hammersley-type sofa with hole radius `r`. -/
def hsofa : Set ℝ² :=
  {p | 0 ≤ p 1 ∧ r ^ 2 ≤ (p 0 + r) ^ 2 + p 1 ^ 2 ∧
    ((0 ≤ p 0 ∧ p 0 ^ 2 + p 1 ^ 2 ≤ 1) ∨ (-(2 * r) ≤ p 0 ∧ p 0 ≤ 0 ∧ p 1 ≤ 1) ∨
      (p 0 ≤ -(2 * r) ∧ (p 0 + 2 * r) ^ 2 + p 1 ^ 2 ≤ 1))}

lemma mem_hsofa {p : ℝ²} : p ∈ hsofa r ↔ 0 ≤ p 1 ∧ r ^ 2 ≤ (p 0 + r) ^ 2 + p 1 ^ 2 ∧
    ((0 ≤ p 0 ∧ p 0 ^ 2 + p 1 ^ 2 ≤ 1) ∨ (-(2 * r) ≤ p 0 ∧ p 0 ≤ 0 ∧ p 1 ≤ 1) ∨
      (p 0 ≤ -(2 * r) ∧ (p 0 + 2 * r) ^ 2 + p 1 ^ 2 ≤ 1)) := Iff.rfl

/-- The inner corner of the hallway, in the sofa's frame, at angle `t`. -/
def hcorner (t : ℝ) : ℝ² := (2 * r * sin t) • v t

/-- The motion: at time `τ` rotate clockwise by `πτ/2` about the moving inner corner. -/
def hmotion (τ : I) : E(2) :=
  rotateTranslate ((-(π / 2 * (τ : ℝ)) : ℝ) : Real.Angle) (-(hcorner r (π / 2 * (τ : ℝ))))

lemma hmotion_apply (τ : I) (q : ℝ²) :
    hmotion r τ q = rot (-(π / 2 * (τ : ℝ))) (q - hcorner r (π / 2 * (τ : ℝ))) := by
  rw [hmotion, rotateTranslate_apply_eq_rot, sub_eq_add_neg]

lemma inner_hcorner_u (t : ℝ) : ⟪hcorner r t, u t⟫ = 0 := by
  rw [hcorner, real_inner_smul_left, inner_v_u, mul_zero]

lemma inner_hcorner_v (t : ℝ) : ⟪hcorner r t, v t⟫ = 2 * r * sin t := by
  rw [hcorner, real_inner_smul_left, inner_v_v, mul_one]

lemma hmotion_coord_zero (τ : I) (q : ℝ²) :
    hmotion r τ q 0 = ⟪q, u (π / 2 * (τ : ℝ))⟫ := by
  rw [hmotion_apply, rot_neg_coord_zero, inner_sub_left, inner_hcorner_u, sub_zero]

lemma hmotion_coord_one (τ : I) (q : ℝ²) :
    hmotion r τ q 1 = ⟪q, v (π / 2 * (τ : ℝ))⟫ - 2 * r * sin (π / 2 * (τ : ℝ)) := by
  rw [hmotion_apply, rot_neg_coord_one, inner_sub_left, inner_hcorner_v]

lemma continuous_hcorner : Continuous (hcorner r) := by
  unfold hcorner
  exact (continuous_const.mul continuous_sin).smul continuous_v

lemma continuous_hmotion : Continuous (hmotion r) := by
  refine continuous_motion_of_continuous_apply fun q => ?_
  simp only [hmotion_apply]
  have hτ : Continuous fun τ : I => π / 2 * (τ : ℝ) := by fun_prop
  exact continuous_rot_apply hτ.neg (continuous_const.sub ((continuous_hcorner r).comp hτ))

lemma hmotion_zero : hmotion r 0 = AffineIsometryEquiv.refl ℝ ℝ² := by
  ext q : 1
  rw [hmotion_apply]
  simp [hcorner, rot_zero]

/-! ### The three estimates along the motion -/

variable {r}

lemma angle_bounds (τ : I) : 0 ≤ π / 2 * (τ : ℝ) ∧ π / 2 * (τ : ℝ) ≤ π / 2 :=
  ⟨mul_nonneg (by positivity) τ.2.1, mul_le_of_le_one_right (by positivity) τ.2.2⟩

/-- Outer wall `a(t)`: `⟪q, u_t⟫ ≤ 1`. -/
lemma inner_u_le_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ π / 2) (hr : 0 < r) {q : ℝ²}
    (hq : q ∈ hsofa r) : ⟪q, u t⟫ ≤ 1 := by
  obtain ⟨hs, hc⟩ := sin_cos_nonneg ht0 ht1
  have hcs := sin_sq_add_cos_sq t
  rw [inner_eq, u_coord_zero, u_coord_one]
  obtain ⟨hy, -, hpiece⟩ := hq
  rcases hpiece with ⟨hx, hd⟩ | ⟨hx1, hx2, hy1⟩ | ⟨hx, hd⟩
  · have e : (q 0 * cos t + q 1 * sin t) ^ 2 + (q 0 * sin t - q 1 * cos t) ^ 2
        = q 0 ^ 2 + q 1 ^ 2 := by linear_combination (q 0 ^ 2 + q 1 ^ 2) * hcs
    exact le_one_of_sq_le_one (by nlinarith [sq_nonneg (q 0 * sin t - q 1 * cos t)])
  · nlinarith [mul_nonneg (neg_nonneg.2 hx2) hc, mul_le_mul_of_nonneg_right hy1 hs, sin_le_one t]
  · have hy1 : q 1 ≤ 1 := le_one_of_sq_le_one (by nlinarith [sq_nonneg (q 0 + 2 * r)])
    have hx2 : q 0 ≤ 0 := by linarith
    nlinarith [mul_nonneg (neg_nonneg.2 hx2) hc, mul_le_mul_of_nonneg_right hy1 hs, sin_le_one t]

/-- Outer wall `c(t)`: `⟪q, v_t⟫ ≤ 1 + 2 r sin t`. -/
lemma inner_v_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ π / 2) (hr : 0 < r) {q : ℝ²}
    (hq : q ∈ hsofa r) : ⟪q, v t⟫ ≤ 1 + 2 * r * sin t := by
  obtain ⟨hs, hc⟩ := sin_cos_nonneg ht0 ht1
  have hcs := sin_sq_add_cos_sq t
  rw [inner_eq, v_coord_zero, v_coord_one]
  obtain ⟨hy, -, hpiece⟩ := hq
  have hrs : 0 ≤ 2 * r * sin t := by positivity
  rcases hpiece with ⟨hx, hd⟩ | ⟨hx1, hx2, hy1⟩ | ⟨hx, hd⟩
  · have e : (q 0 * -sin t + q 1 * cos t) ^ 2 + (q 0 * cos t + q 1 * sin t) ^ 2
        = q 0 ^ 2 + q 1 ^ 2 := by linear_combination (q 0 ^ 2 + q 1 ^ 2) * hcs
    have := le_one_of_sq_le_one (a := q 0 * -sin t + q 1 * cos t)
      (by nlinarith [sq_nonneg (q 0 * cos t + q 1 * sin t)])
    linarith
  · nlinarith [mul_le_mul_of_nonneg_right (by linarith : -q 0 ≤ 2 * r) hs,
      mul_le_mul_of_nonneg_right hy1 hc, cos_le_one t]
  · have e : ((q 0 + 2 * r) * -sin t + q 1 * cos t) ^ 2 + ((q 0 + 2 * r) * cos t + q 1 * sin t) ^ 2
        = (q 0 + 2 * r) ^ 2 + q 1 ^ 2 := by
      linear_combination ((q 0 + 2 * r) ^ 2 + q 1 ^ 2) * hcs
    have := le_one_of_sq_le_one (a := (q 0 + 2 * r) * -sin t + q 1 * cos t)
      (by nlinarith [sq_nonneg ((q 0 + 2 * r) * cos t + q 1 * sin t)])
    nlinarith

/-- Inner walls `b(t), d(t)`: the sofa avoids the open inner quarter-plane
`{⟪q, u_t⟫ < 0, ⟪q, v_t⟫ < 2 r sin t}` (it meets the upper half plane only inside the hole). -/
lemma not_mem_niche {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ π / 2) {q : ℝ²}
    (hq : q ∈ hsofa r) : ¬ (⟪q, u t⟫ < 0 ∧ ⟪q, v t⟫ < 2 * r * sin t) := by
  rintro ⟨ha, hb⟩
  obtain ⟨hs, hc⟩ := sin_cos_nonneg ht0 ht1
  have hcs := sin_sq_add_cos_sq t
  obtain ⟨hy, hhole, -⟩ := hq
  rw [inner_eq, u_coord_zero, u_coord_one] at ha
  rw [inner_eq, v_coord_zero, v_coord_one] at hb
  -- `α = ⟪q, u_t⟫`, `β = ⟪q, v_t⟫`
  obtain ⟨α, hα⟩ : ∃ α, α = q 0 * cos t + q 1 * sin t := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = q 0 * -sin t + q 1 * cos t := ⟨_, rfl⟩
  rw [← hα] at ha
  rw [← hβ] at hb
  have hx : q 0 = α * cos t - β * sin t := by rw [hα, hβ]; linear_combination (-(q 0)) * hcs
  have hy' : q 1 = α * sin t + β * cos t := by rw [hα, hβ]; linear_combination (-(q 1)) * hcs
  have hnorm : q 0 ^ 2 + q 1 ^ 2 = α ^ 2 + β ^ 2 := by
    rw [hα, hβ]; linear_combination (-(q 0 ^ 2 + q 1 ^ 2)) * hcs
  rcases hs.eq_or_lt with hs0 | hs0
  · -- `sin t = 0`: then `β < 0` and `cos t = 1`, so `q 1 = β < 0`
    have hc1 : cos t = 1 := by nlinarith
    rw [← hs0, hc1] at hy'
    rw [← hs0] at hb
    nlinarith
  rcases hc.eq_or_lt with hc0 | hc0
  · -- `cos t = 0`: then `sin t = 1`, so `q 1 = α < 0`
    have hs1 : sin t = 1 := by nlinarith
    rw [← hc0, hs1] at hy'
    nlinarith
  -- the generic case
  have hβpos : 0 < β := by nlinarith [mul_neg_of_neg_of_pos ha hs0]
  have hαgt : -(2 * r * cos t) < α := by
    nlinarith [mul_lt_mul_of_pos_right hb hc0]
  have hF : q 0 ^ 2 + q 1 ^ 2 + 2 * r * q 0 < 0 := by
    rw [hnorm, hx]
    nlinarith [mul_neg_of_neg_of_pos ha (by linarith : 0 < α + 2 * r * cos t),
      mul_neg_of_pos_of_neg hβpos (by linarith : β - 2 * r * sin t < 0)]
  nlinarith

variable (r)

/-! ### The sofa is a moving sofa -/

lemma isClosed_hsofa : IsClosed (hsofa r) := by
  have c0 := continuous_coord 0
  have c1 := continuous_coord 1
  unfold hsofa
  simp only [Set.ofPred_and, Set.ofPred_or]
  refine (isClosed_le continuous_const c1).inter ((isClosed_le continuous_const (by fun_prop)).inter
    (((isClosed_le continuous_const c0).inter (isClosed_le (by fun_prop) continuous_const)).union
      (((isClosed_le continuous_const c0).inter
        ((isClosed_le c0 continuous_const).inter (isClosed_le c1 continuous_const))).union
      ((isClosed_le c0 continuous_const).inter (isClosed_le (by fun_prop) continuous_const)))))

variable {r}

lemma isPreconnected_hsofa (hr0 : 0 < r) (hr1 : r ≤ 1) : IsPreconnected (hsofa r) := by
  set T := (fun ab : ℝ × ℝ => pt ab.1 ab.2) '' (Icc (-(2 * r)) 0 ×ˢ Icc r 1) with hT
  have hTc : IsPreconnected T :=
    (isPreconnected_Icc.prod isPreconnected_Icc).image _ continuous_pt.continuousOn
  have hTS : T ⊆ hsofa r := by
    rintro _ ⟨⟨a, b⟩, ⟨⟨ha1, ha2⟩, ⟨hb1, hb2⟩⟩, rfl⟩
    simp only [mem_hsofa, pt_zero, pt_one]
    exact ⟨by linarith, by nlinarith [sq_nonneg (a + r)], Or.inr (Or.inl ⟨ha1, ha2, hb2⟩)⟩
  have h01 : pt 0 1 ∈ T := ⟨(0, 1), ⟨⟨by linarith, le_rfl⟩, ⟨hr1, le_rfl⟩⟩, rfl⟩
  -- vertical segments from a point of the rectangle up to the top edge
  have hV : ∀ a y, -(2 * r) ≤ a → a ≤ 0 → 0 ≤ y → r ^ 2 ≤ (a + r) ^ 2 + y ^ 2 → y ≤ 1 →
      ∃ C ⊆ hsofa r, pt 0 1 ∈ C ∧ pt a y ∈ C ∧ IsPreconnected C := by
    intro a y ha1 ha2 hy0 hhole hy1
    refine ⟨((fun b => pt a b) '' Icc y 1) ∪ T, union_subset ?_ hTS, Or.inr h01,
      Or.inl ⟨y, ⟨le_rfl, hy1⟩, rfl⟩, ?_⟩
    · rintro _ ⟨b, ⟨hb1, hb2⟩, rfl⟩
      simp only [mem_hsofa, pt_zero, pt_one]
      exact ⟨by linarith, by nlinarith [mul_nonneg hy0 (sub_nonneg.2 hb1)],
        Or.inr (Or.inl ⟨ha1, ha2, hb2⟩)⟩
    · exact IsPreconnected.union (pt a 1) ⟨1, ⟨hy1, le_rfl⟩, rfl⟩
        ⟨(a, 1), ⟨⟨ha1, ha2⟩, ⟨hr1, le_rfl⟩⟩, rfl⟩
        (isPreconnected_Icc.image _ (continuous_pt_right a).continuousOn) hTc
  refine isPreconnected_of_forall (pt 0 1) fun p hp => ?_
  obtain ⟨hy, hhole, hpiece⟩ := hp
  rcases hpiece with ⟨hx, hd⟩ | ⟨hx1, hx2, hy1⟩ | ⟨hx, hd⟩
  · -- right quarter disc: slide left to `x = 0`, then up
    have hy1 : p 1 ≤ 1 := le_one_of_sq_le_one (by nlinarith)
    obtain ⟨C, hCS, hC0, hC1, hCc⟩ :=
      hV 0 (p 1) (by linarith) le_rfl hy (by nlinarith) hy1
    refine ⟨((fun a => pt a (p 1)) '' Icc 0 (p 0)) ∪ C, union_subset ?_ hCS, Or.inr hC0,
      Or.inl ⟨p 0, ⟨hx, le_rfl⟩, (eq_pt p).symm⟩, ?_⟩
    · rintro _ ⟨a, ⟨ha1, ha2⟩, rfl⟩
      simp only [mem_hsofa, pt_zero, pt_one]
      exact ⟨hy, by nlinarith [mul_nonneg ha1 hr0.le],
        Or.inl ⟨ha1, by nlinarith [mul_le_mul ha2 ha2 ha1 hx]⟩⟩
    · exact IsPreconnected.union (pt 0 (p 1)) ⟨0, ⟨le_rfl, hx⟩, rfl⟩ hC1
        (isPreconnected_Icc.image _ (continuous_pt_left _).continuousOn) hCc
  · obtain ⟨C, hCS, hC0, hC1, hCc⟩ := hV (p 0) (p 1) hx1 hx2 hy hhole hy1
    refine ⟨C, hCS, hC0, ?_, hCc⟩
    rw [eq_pt p]; exact hC1
  · -- left quarter disc: slide right to `x = -2r`, then up
    have hy1 : p 1 ≤ 1 := le_one_of_sq_le_one (by nlinarith [sq_nonneg (p 0 + 2 * r)])
    obtain ⟨C, hCS, hC0, hC1, hCc⟩ :=
      hV (-(2 * r)) (p 1) le_rfl (by linarith) hy (by nlinarith) hy1
    refine ⟨((fun a => pt a (p 1)) '' Icc (p 0) (-(2 * r))) ∪ C, union_subset ?_ hCS,
      Or.inr hC0, Or.inl ⟨p 0, ⟨le_rfl, hx⟩, (eq_pt p).symm⟩, ?_⟩
    · rintro _ ⟨a, ⟨ha1, ha2⟩, rfl⟩
      simp only [mem_hsofa, pt_zero, pt_one]
      exact ⟨hy, by nlinarith, Or.inr (Or.inr ⟨ha2, by nlinarith⟩)⟩
    · exact IsPreconnected.union (pt (-(2 * r)) (p 1)) ⟨-(2 * r), ⟨hx, le_rfl⟩, rfl⟩ hC1
        (isPreconnected_Icc.image _ (continuous_pt_left _).continuousOn) hCc

lemma pt_zero_one_mem (hr0 : 0 < r) : pt 0 1 ∈ hsofa r := by
  simp only [mem_hsofa, pt_zero, pt_one]
  exact ⟨by norm_num, by nlinarith, Or.inr (Or.inl ⟨by linarith, le_rfl, le_rfl⟩)⟩

/-- **Hammersley's sofa is a moving sofa** (for every hole radius `0 < r ≤ 1`). -/
theorem isMovingSofa_hsofa (hr0 : 0 < r) (hr1 : r ≤ 1) : IsMovingSofa (hsofa r) (hmotion r) where
  isConnected := ⟨⟨_, pt_zero_one_mem hr0⟩, isPreconnected_hsofa hr0 hr1⟩
  isClosed := isClosed_hsofa r
  continuous := continuous_hmotion r
  zero := hmotion_zero r
  initial := by
    intro p hp
    rw [mem_horizontalHallway_iff]
    obtain ⟨hy, -, hpiece⟩ := hp
    rcases hpiece with ⟨hx, hd⟩ | ⟨hx1, hx2, hy1⟩ | ⟨hx, hd⟩
    · exact ⟨le_one_of_sq_le_one (by nlinarith), hy, le_one_of_sq_le_one (by nlinarith)⟩
    · exact ⟨by linarith, hy, hy1⟩
    · exact ⟨by linarith, hy,
        le_one_of_sq_le_one (by nlinarith [sq_nonneg (p 0 + 2 * r)])⟩
  subset_hallway := by
    rintro τ _ ⟨q, hq, rfl⟩
    obtain ⟨ht0, ht1⟩ := angle_bounds τ
    rw [hallway_eq_diff, Set.mem_sdiff, mem_Qplus_iff, mem_Qminus_iff, hmotion_coord_zero,
      hmotion_coord_one]
    refine ⟨⟨inner_u_le_one ht0 ht1 hr0 hq, by linarith [inner_v_le ht0 ht1 hr0 hq]⟩, ?_⟩
    rintro ⟨h1, h2⟩
    exact not_mem_niche ht0 ht1 hq ⟨h1, by linarith⟩
  final := by
    rintro _ ⟨q, hq, rfl⟩
    rw [mem_verticalHallway_iff, hmotion_coord_zero, hmotion_coord_one]
    have h1 : π / 2 * ((1 : I) : ℝ) = π / 2 := by simp
    rw [h1, inner_u_pi_div_two, sin_pi_div_two, inner_eq, v_coord_zero, v_coord_one,
      sin_pi_div_two, cos_pi_div_two]
    obtain ⟨hy, -, hpiece⟩ := hq
    rcases hpiece with ⟨hx, hd⟩ | ⟨hx1, hx2, hy1⟩ | ⟨hx, hd⟩
    · refine ⟨hy, le_one_of_sq_le_one (by nlinarith), by nlinarith⟩
    · refine ⟨hy, hy1, by nlinarith⟩
    · have hx' : -1 ≤ q 0 + 2 * r := by nlinarith [sq_nonneg (q 1)]
      refine ⟨hy, le_one_of_sq_le_one (by nlinarith [sq_nonneg (q 0 + 2 * r)]), by nlinarith⟩

end HSofa

end Sofa
