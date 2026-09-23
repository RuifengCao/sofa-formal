/-
# Sofa/GerverPath.lean — Gerver's rotation path `p` (upstream): first facts

The upstream Gerver sofa is `gerversSofa = sofaOfRotateTranslatePath p`, where Gerver's path `p`
is built from the radius function `r` and its integrals `x`, `y` (Gerver 1992, Thm 2).  Here:

* enclosures of the constants: `φ`, `θ` to within `2⁻³⁰` (`GerverSpec.lean`), `A`, `B` to within
  `≈ 10⁻⁸` (`A_mem`, `B_mem`: one kernel-checked interval evaluation);
* `r` is measurable with `0 ≤ r ≤ 3/2` (`r_nonneg`, `r_le`), hence integrable on every interval;
* `x`, `y` and `p` are continuous (`continuous_p`);
* `y 0 = 1` (closed-form integration on the four pieces; the identity is `E₃ − sin θ · E₄ = 0`),
  hence `p 0 = 0` (`p_zero`);
* Gerver's motion `gmotion τ = (rotateTranslate α (p α))⁻¹`, `α = πτ/2`: continuous, the identity
  at `τ = 0`; so the upstream `isMovingSofa_gerversSofa` holds as soon as `gerversSofa` is
  connected (`isMovingSofa_gerversSofa_of_isConnected`).

STATUS: [PROOF-C-local] round 38 (2026-09-23, Opus 5.5).
-/
import Sofa.GerverSpec
import Sofa.Motion

noncomputable section

open Real Set MeasureTheory intervalIntegral MovingSofa
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa.GP

open GC IA
open MovingSofa.GerversSofa (A B φ θ r)

/-! ## The constants -/

lemma φ_mem : tbox.1.Mem φ := gerver_mem_tbox.1

lemma θ_mem : tbox.2.Mem θ := gerver_mem_tbox.2

/-- `A = N₁ / (3 cos φ − cos θ)` and `B = A κ + c₀`. -/
lemma A_eq : A = N1E.eval (envOf φ θ) / denE.eval (envOf φ θ) := by
  obtain ⟨-, -, -, -, -, e1, -, e3, -⟩ := spec_iff.1 gerver_spec
  have hden : 0 < denE.eval (envOf φ θ) :=
    (pos_on_target (φ := φ) (θ := θ) (tbox_sub gerver_mem_tbox)).1
  have e13 := eq1_sub_eq3 A B φ θ
  rw [e1, e3] at e13
  rw [eq_div_iff hden.ne']
  linarith

lemma B_eq : B = A * kkE.eval (envOf φ θ) + c0E.eval (envOf φ θ) := by
  obtain ⟨-, -, -, -, -, -, -, -, e4⟩ := spec_iff.1 gerver_spec
  have := eq4_eq A B φ θ
  rw [e4] at this
  linarith

/-- Lower end of the enclosure of `A`, in units of `2⁻⁴⁰` (`A ≈ 0.0944265608`). -/
def aLo : ℤ := 103823098641
def aHi : ℤ := 103823104599
/-- Lower end of the enclosure of `B`, in units of `2⁻⁴⁰` (`B ≈ 1.3992037273`). -/
def bLo : ℤ := 1538440760070
def bHi : ℤ := 1538440775596

/-- The interval enclosures of `N₁`, `3 cos φ − cos θ`, `κ`, `c₀` on the tight box. -/
def tb : ℕ → Iv := boxOf tbox.1.lo tbox.1.hi tbox.2.lo tbox.2.hi

/-- The check of the enclosures of `A = N₁ / den` and `B = A κ + c₀`. -/
def abOK : Bool :=
  decide (0 < (denE.ieval tb).lo) && decide (0 < (kkE.ieval tb).lo) && decide (0 ≤ aLo)
    && decide ((N1E.ieval tb).hi * S ≤ aHi * (denE.ieval tb).lo)
    && decide (aLo * (denE.ieval tb).hi ≤ (N1E.ieval tb).lo * S)
    && decide (aHi * (kkE.ieval tb).hi + (c0E.ieval tb).hi * S ≤ bHi * S)
    && decide (bLo * S ≤ aLo * (kkE.ieval tb).lo + (c0E.ieval tb).lo * S)

theorem abOK_true : abOK = true := by
  decide +kernel

lemma tb_mem : ∀ i, (tb i).Mem (envOf φ θ i) := mem_boxOf φ_mem θ_mem

lemma lo_le {J : Iv} {x : ℝ} (h : J.Mem x) : (J.lo : ℝ) ≤ x * S := by
  have := h.1; rwa [div_le_iff₀ S_pos] at this

lemma le_hi {J : Iv} {x : ℝ} (h : J.Mem x) : x * S ≤ J.hi := by
  have := h.2; rwa [le_div_iff₀ S_pos] at this

/-- **Enclosure of `A`**: `A ∈ [aLo, aHi] · 2⁻⁴⁰`. -/
theorem A_mem : (⟨aLo, aHi⟩ : Iv).Mem A := by
  have h := abOK_true
  unfold abOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hD, -⟩, ha0⟩, h1⟩, h2⟩, -⟩, -⟩ := h
  have hS := S_pos
  have hN := IE.mem_ieval tb_mem N1E
  have hDm := IE.mem_ieval tb_mem denE
  have hd0 : 0 < denE.eval (envOf φ θ) :=
    (div_pos (by exact_mod_cast hD) hS).trans_le hDm.1
  have h1' : ((N1E.ieval tb).hi : ℝ) * S ≤ aHi * (denE.ieval tb).lo := by exact_mod_cast h1
  have h2' : (aLo : ℝ) * (denE.ieval tb).hi ≤ (N1E.ieval tb).lo * S := by exact_mod_cast h2
  have ha0' : (0 : ℝ) ≤ aLo := by exact_mod_cast ha0
  have nlo := lo_le hN
  have nhi := le_hi hN
  have dlo := lo_le hDm
  have dhi := le_hi hDm
  rw [A_eq]
  constructor
  · rw [div_le_div_iff₀ hS hd0]
    -- aLo * den ≤ N₁ * S
    have e1 : (aLo : ℝ) * (denE.eval (envOf φ θ) * S) ≤ aLo * (denE.ieval tb).hi :=
      mul_le_mul_of_nonneg_left dhi ha0'
    have e2 : ((N1E.ieval tb).lo : ℝ) * S ≤ N1E.eval (envOf φ θ) * S * S :=
      mul_le_mul_of_nonneg_right nlo hS.le
    have : (aLo : ℝ) * denE.eval (envOf φ θ) * S ≤ N1E.eval (envOf φ θ) * S * S := by
      nlinarith
    exact le_of_mul_le_mul_right (by linarith) hS
  · rw [div_le_div_iff₀ hd0 hS]
    have haH : (0 : ℝ) ≤ aHi := by
      have : (aLo : ℝ) ≤ aHi := by
        have c : aLo ≤ aHi := by decide
        exact_mod_cast c
      linarith
    have e1 : (aHi : ℝ) * (denE.ieval tb).lo ≤ aHi * (denE.eval (envOf φ θ) * S) :=
      mul_le_mul_of_nonneg_left dlo haH
    have e2 : N1E.eval (envOf φ θ) * S * S ≤ ((N1E.ieval tb).hi : ℝ) * S :=
      mul_le_mul_of_nonneg_right nhi hS.le
    have : N1E.eval (envOf φ θ) * S * S ≤ (aHi : ℝ) * denE.eval (envOf φ θ) * S := by
      nlinarith
    exact le_of_mul_le_mul_right (by linarith) hS

/-- **Enclosure of `B`**: `B ∈ [bLo, bHi] · 2⁻⁴⁰`. -/
theorem B_mem : (⟨bLo, bHi⟩ : Iv).Mem B := by
  have h := abOK_true
  unfold abOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, hK⟩, ha0⟩, -⟩, -⟩, h3⟩, h4⟩ := h
  have hS := S_pos
  have hKm := IE.mem_ieval tb_mem kkE
  have hCm := IE.mem_ieval tb_mem c0E
  have hk0 : 0 < kkE.eval (envOf φ θ) := (div_pos (by exact_mod_cast hK) hS).trans_le hKm.1
  have hA := A_mem
  have h3' : (aHi : ℝ) * (kkE.ieval tb).hi + (c0E.ieval tb).hi * S ≤ bHi * S := by
    exact_mod_cast h3
  have h4' : (bLo : ℝ) * S ≤ aLo * (kkE.ieval tb).lo + (c0E.ieval tb).lo * S := by
    exact_mod_cast h4
  have ha0' : (0 : ℝ) ≤ aLo := by exact_mod_cast ha0
  have alo := lo_le hA
  have ahi := le_hi hA
  have klo := lo_le hKm
  have khi := le_hi hKm
  have clo := lo_le hCm
  have chi := le_hi hCm
  have hA0 : 0 ≤ A := by
    have : (0 : ℝ) ≤ A * S := ha0'.trans alo
    exact nonneg_of_mul_nonneg_left this hS
  rw [B_eq]
  constructor
  · rw [div_le_iff₀ hS]
    -- bLo ≤ (A κ + c₀) S
    have e1 : (aLo : ℝ) * (kkE.ieval tb).lo ≤ A * S * (kkE.eval (envOf φ θ) * S) :=
      mul_le_mul alo klo (by exact_mod_cast hK.le) (by positivity)
    have : (bLo : ℝ) * S ≤ (A * kkE.eval (envOf φ θ) + c0E.eval (envOf φ θ)) * S * S := by
      nlinarith
    nlinarith
  · rw [le_div_iff₀ hS]
    have e1 : A * S * (kkE.eval (envOf φ θ) * S) ≤ (aHi : ℝ) * (kkE.ieval tb).hi :=
      mul_le_mul ahi khi (by positivity) ((mul_nonneg hA0 hS.le).trans ahi)
    have : (A * kkE.eval (envOf φ θ) + c0E.eval (envOf φ θ)) * S * S ≤ (bHi : ℝ) * S := by
      nlinarith
    nlinarith

/-- Coarse bounds on the constants. -/
lemma bounds : 39 / 1000 < φ ∧ φ < 40 / 1000 ∧ 681 / 1000 < θ ∧ θ < 682 / 1000 ∧
    94 / 1000 < A ∧ A < 95 / 1000 ∧ 1399 / 1000 < B ∧ B < 1400 / 1000 := by
  have hS := S_pos
  obtain ⟨p1, p2⟩ := φ_mem
  obtain ⟨t1, t2⟩ := θ_mem
  obtain ⟨a1, a2⟩ := A_mem
  obtain ⟨b1, b2⟩ := B_mem
  simp only [tbox, cφ₀, cθ₀, aLo, aHi, bLo, bHi, S] at p1 p2 t1 t2 a1 a2 b1 b2
  norm_num at p1 p2 t1 t2 a1 a2 b1 b2
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

/-! ## The radius function `r` -/

lemma r_def (α : ℝ) : r α = if α ≤ φ then 1 / 2 else if α ≤ θ then (1 + A + α - φ) / 2
    else if α ≤ π / 2 - θ then A + α - φ else if α ≤ π / 2 - φ then
      B - (π / 2 - α - φ) * (1 + A) / 2 - (π / 2 - α - φ) ^ 2 / 4 else 0 := rfl

lemma measurable_r : Measurable r := by
  have h : r = fun α => if α ≤ φ then 1 / 2 else if α ≤ θ then (1 + A + α - φ) / 2
      else if α ≤ π / 2 - θ then A + α - φ else if α ≤ π / 2 - φ then
        B - (π / 2 - α - φ) * (1 + A) / 2 - (π / 2 - α - φ) ^ 2 / 4 else 0 := funext r_def
  rw [h]
  refine Measurable.ite measurableSet_Iic measurable_const ?_
  refine Measurable.ite measurableSet_Iic (by fun_prop) ?_
  refine Measurable.ite measurableSet_Iic (by fun_prop) ?_
  exact Measurable.ite measurableSet_Iic (by fun_prop) measurable_const

/-- `0 ≤ r ≤ 3/2`. -/
lemma r_nonneg_le (α : ℝ) : 0 ≤ r α ∧ r α ≤ 3 / 2 := by
  obtain ⟨p1, p2, t1, t2, a1, a2, b1, b2⟩ := bounds
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  rw [r_def]
  split_ifs with h1 h2 h3 h4
  · norm_num
  · constructor <;> linarith
  · constructor <;> linarith
  · set s := π / 2 - α - φ with hs
    have hs0 : 0 ≤ s := by linarith
    have hs1 : s < θ - φ := by linarith
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hs1.le (by linarith : (0 : ℝ) ≤ 1 + A),
        mul_le_mul hs1.le hs1.le hs0 (by linarith : (0 : ℝ) ≤ θ - φ)]
    · nlinarith [mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ 1 + A), sq_nonneg s]
  · norm_num

lemma intervalIntegrable_r (a b : ℝ) : IntervalIntegrable r volume a b := by
  refine (intervalIntegrable_const (c := (3 / 2 : ℝ))).mono_fun
    measurable_r.aestronglyMeasurable (Filter.Eventually.of_forall fun α => ?_)
  obtain ⟨h0, h1⟩ := r_nonneg_le α
  simp only [Real.norm_eq_abs, abs_of_nonneg h0]
  norm_num
  linarith

lemma intervalIntegrable_r_mul {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    IntervalIntegrable (fun t => r t * f t) volume a b :=
  (intervalIntegrable_r a b).mul_continuousOn hf.continuousOn

/-! ## `x`, `y` and `p` are continuous -/

lemma y_eq (α : ℝ) : GerversSofa.y α = -∫ t in (π / 2 - φ)..α, r t * sin t := by
  rw [GerversSofa.y, integral_symm]

lemma x_eq (α : ℝ) : GerversSofa.x α = 1 + ∫ t in (π / 2 - φ)..α, r t * cos t := by
  rw [GerversSofa.x, integral_symm, sub_neg_eq_add]

lemma continuous_y : Continuous GerversSofa.y := by
  have : GerversSofa.y = fun α => -∫ t in (π / 2 - φ)..α, r t * sin t := funext y_eq
  rw [this]
  exact (continuous_primitive (fun a b => intervalIntegrable_r_mul continuous_sin a b) _).neg

lemma continuous_x : Continuous GerversSofa.x := by
  have : GerversSofa.x = fun α => 1 + ∫ t in (π / 2 - φ)..α, r t * cos t := funext x_eq
  rw [this]
  exact continuous_const.add
    (continuous_primitive (fun a b => intervalIntegrable_r_mul continuous_cos a b) _)

lemma x_end : GerversSofa.x (π / 2 - φ) = 1 := by
  unfold GerversSofa.x; rw [integral_same, sub_zero]

lemma y_end : GerversSofa.y (π / 2 - φ) = 0 := by
  unfold GerversSofa.y; rw [integral_same]

/-- The first coordinate of `p`. -/
def p₁ (α : ℝ) : ℝ :=
  if α ≤ φ then cos α - 1
  else GerversSofa.x (π / 2 - α) * cos α + GerversSofa.y (π / 2 - α) * sin α - 1

/-- The second coordinate of `p`. -/
def p₂ (α : ℝ) : ℝ :=
  if α ≤ π / 2 - φ then
    GerversSofa.y α * cos α - (4 * GerversSofa.x 0 - 2 - GerversSofa.x α) * sin α - 1
  else -(4 * GerversSofa.x 0 - 3) * sin α - 1

lemma p_coord_zero (α : ℝ) : GerversSofa.p α 0 = p₁ α := rfl

lemma p_coord_one (α : ℝ) : GerversSofa.p α 1 = p₂ α := rfl

lemma p_eq (α : ℝ) : GerversSofa.p α = pt (p₁ α) (p₂ α) := by
  rw [eq_pt (GerversSofa.p α), p_coord_zero, p_coord_one]

lemma continuous_p₁ : Continuous p₁ := by
  refine Continuous.if_le (by fun_prop)
    (((continuous_x.comp (continuous_const.sub continuous_id)).mul continuous_cos).add
      ((continuous_y.comp (continuous_const.sub continuous_id)).mul continuous_sin) |>.sub
        continuous_const) continuous_id continuous_const fun α h => ?_
  subst h
  rw [x_end, y_end]
  ring

lemma continuous_p₂ : Continuous p₂ := by
  refine Continuous.if_le ((continuous_y.mul continuous_cos).sub
    ((continuous_const.sub continuous_x).mul continuous_sin) |>.sub continuous_const)
    (by fun_prop) continuous_id continuous_const fun α h => ?_
  subst h
  rw [x_end, y_end]
  ring

lemma continuous_p : Continuous GerversSofa.p := by
  have : GerversSofa.p = fun α => pt (p₁ α) (p₂ α) := funext p_eq
  rw [this]
  exact continuous_pt.comp (continuous_p₁.prodMk continuous_p₂)

/-! ## `y 0 = 1` and `p 0 = 0` -/

/-- `∫ (a + b t + c t²) sin t = [−(a + b t + c t²) cos t + (b + 2 c t) sin t + 2 c cos t]`. -/
lemma integral_quad_mul_sin (a b c l m : ℝ) :
    ∫ t in l..m, (a + b * t + c * t ^ 2) * sin t =
      (-(a + b * m + c * m ^ 2) * cos m + (b + 2 * c * m) * sin m + 2 * c * cos m)
        - (-(a + b * l + c * l ^ 2) * cos l + (b + 2 * c * l) * sin l + 2 * c * cos l) := by
  refine integral_eq_sub_of_hasDerivAt
    (f := fun t => -(a + b * t + c * t ^ 2) * cos t + (b + 2 * c * t) * sin t + 2 * c * cos t)
    (fun t _ => ?_) ((by fun_prop : Continuous
      fun t => (a + b * t + c * t ^ 2) * sin t).intervalIntegrable _ _)
  have hg : HasDerivAt (fun t => a + b * t + c * t ^ 2) (b + 2 * c * t) t :=
    ((((hasDerivAt_id' t).const_mul b).const_add a).fun_add
      ((hasDerivAt_pow 2 t).const_mul c)).congr_deriv (by norm_num; ring)
  have hg' : HasDerivAt (fun t => b + 2 * c * t) (2 * c) t :=
    (((hasDerivAt_id' t).const_mul (2 * c)).const_add b).congr_deriv (by ring)
  exact (((hg.fun_neg.fun_mul (hasDerivAt_cos t)).fun_add (hg'.fun_mul (hasDerivAt_sin t))).fun_add
    ((hasDerivAt_cos t).const_mul (2 * c))).congr_deriv (by ring)

/-- On each piece, `r` is a polynomial of degree at most two. -/
lemma r_of_le_φ {t : ℝ} (ht : t ≤ φ) : r t = 1 / 2 := by
  rw [r_def, if_pos ht]

lemma r_piece₂ {t : ℝ} (ht : t ∈ Ioc φ θ) : r t = (1 + A + t - φ) / 2 := by
  rw [r_def, if_neg (not_le.2 ht.1), if_pos ht.2]

lemma r_piece₃ {t : ℝ} (ht : t ∈ Ioc θ (π / 2 - θ)) : r t = A + t - φ := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  rw [r_def, if_neg (by linarith [ht.1]), if_neg (not_le.2 ht.1), if_pos ht.2]

lemma r_piece₄ {t : ℝ} (ht : t ∈ Ioc (π / 2 - θ) (π / 2 - φ)) :
    r t = B - (π / 2 - t - φ) * (1 + A) / 2 - (π / 2 - t - φ) ^ 2 / 4 := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  rw [r_def, if_neg (by linarith [ht.1]), if_neg (by linarith [ht.1]),
    if_neg (not_le.2 ht.1), if_pos ht.2]

/-- **`y 0 = 1`**: the height of Gerver's sofa is one (the identity is `E₃ − sin θ · E₄ = 0`). -/
theorem y_zero : GerversSofa.y 0 = 1 := by
  obtain ⟨p1, p2, t1, t2, -⟩ := bounds
  have hpi := Real.pi_gt_d2
  obtain ⟨-, -, -, -, -, -, -, e3, e4⟩ := spec_iff.1 gerver_spec
  have hi : ∀ a b, IntervalIntegrable (fun t => r t * sin t) volume a b :=
    intervalIntegrable_r_mul continuous_sin
  have split : GerversSofa.y 0 = (∫ t in (0 : ℝ)..φ, r t * sin t) + (∫ t in φ..θ, r t * sin t)
      + (∫ t in θ..(π / 2 - θ), r t * sin t) + ∫ t in (π / 2 - θ)..(π / 2 - φ), r t * sin t := by
    rw [GerversSofa.y, integral_add_adjacent_intervals (hi _ _) (hi _ _),
      integral_add_adjacent_intervals (hi _ _) (hi _ _),
      integral_add_adjacent_intervals (hi _ _) (hi _ _)]
  have i1 : ∫ t in (0 : ℝ)..φ, r t * sin t = ∫ t in (0 : ℝ)..φ, (1 / 2 + 0 * t + 0 * t ^ 2) * sin t := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le (by linarith)] at ht
    rw [r_of_le_φ ht.2]; ring
  have i2 : ∫ t in φ..θ, r t * sin t
      = ∫ t in φ..θ, ((1 + A - φ) / 2 + 1 / 2 * t + 0 * t ^ 2) * sin t := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le (by linarith)] at ht
    rw [r_piece₂ ht]; ring
  have i3 : ∫ t in θ..(π / 2 - θ), r t * sin t
      = ∫ t in θ..(π / 2 - θ), ((A - φ) + 1 * t + 0 * t ^ 2) * sin t := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le (by linarith)] at ht
    rw [r_piece₃ ht]; ring
  have i4 : ∫ t in (π / 2 - θ)..(π / 2 - φ), r t * sin t
      = ∫ t in (π / 2 - θ)..(π / 2 - φ), ((B - (π / 2 - φ) * (1 + A) / 2 - (π / 2 - φ) ^ 2 / 4)
          + ((1 + A) / 2 + (π / 2 - φ) / 2) * t + (-1 / 4) * t ^ 2) * sin t := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
    rw [uIoc_of_le (by linarith)] at ht
    rw [r_piece₄ ht]; ring
  rw [split, i1, i2, i3, i4, integral_quad_mul_sin, integral_quad_mul_sin, integral_quad_mul_sin,
    integral_quad_mul_sin]
  simp only [sin_pi_div_two_sub, cos_pi_div_two_sub, sin_zero, cos_zero]
  simp only [eq3, eq4] at e3 e4
  linear_combination e3 - sin θ * e4

/-- **`p 0 = 0`**: Gerver's path starts at the origin. -/
theorem p_zero : GerversSofa.p 0 = 0 := by
  obtain ⟨p1, p2, -⟩ := bounds
  rw [p_eq]
  have h1 : p₁ 0 = 0 := by
    rw [p₁, if_pos (by linarith)]; simp
  have h2 : p₂ 0 = 0 := by
    have hpi := Real.pi_gt_d2
    rw [p₂, if_pos (by linarith), y_zero]; simp
  rw [h1, h2]
  ext i; fin_cases i <;> simp

/-! ## Gerver's motion -/

/-- The rotation angle at time `τ`: `α = πτ/2`. -/
def ang (τ : I) : ℝ := π / 2 * (τ : ℝ)

lemma continuous_ang : Continuous ang := by unfold ang; fun_prop

lemma ang_mem (τ : I) : ang τ ∈ Icc (0 : ℝ) (π / 2) :=
  ⟨mul_nonneg (by positivity) τ.2.1, mul_le_of_le_one_right (by positivity) τ.2.2⟩

/-- Gerver's motion: at time `τ`, undo `rotateTranslate α (p α)`. -/
def gmotion (τ : I) : E(2) := (rotateTranslate (ang τ : Real.Angle) (GerversSofa.p (ang τ))).symm

lemma gmotion_apply (τ : I) (z : ℝ²) :
    gmotion τ z = rot (-(ang τ)) z - GerversSofa.p (ang τ) := by
  rw [gmotion, AffineIsometryEquiv.symm_apply_eq, rotateTranslate_apply_eq_rot, sub_add_cancel,
    rot_rot, add_neg_cancel, rot_zero]

lemma continuous_gmotion : Continuous gmotion := by
  refine continuous_motion_of_continuous_apply fun z => ?_
  simp only [gmotion_apply]
  exact (continuous_rot_apply continuous_ang.neg continuous_const).sub
    (continuous_p.comp continuous_ang)

lemma gmotion_zero : gmotion 0 = AffineIsometryEquiv.refl ℝ ℝ² := by
  ext z : 1
  rw [gmotion_apply]
  simp [ang, p_zero, rot_zero]

lemma isClosed_rotateTranslate_image (α : Real.Angle) (q : ℝ²) {s : Set ℝ²} (hs : IsClosed s) :
    IsClosed (rotateTranslate α q '' s) := by
  rw [← AffineIsometryEquiv.coe_toHomeomorph]
  exact (Homeomorph.isClosed_image _).2 hs

lemma isClosed_horizontalHallway : IsClosed horizontalHallway := by
  have : horizontalHallway = {q : ℝ² | q 0 ≤ 1 ∧ 0 ≤ q 1 ∧ q 1 ≤ 1} := by
    ext q; exact mem_horizontalHallway_iff q
  rw [this]
  exact (isClosed_le (continuous_coord 0) continuous_const).inter
    ((isClosed_le continuous_const (continuous_coord 1)).inter
      (isClosed_le (continuous_coord 1) continuous_const))

lemma isClosed_verticalHallway : IsClosed verticalHallway := by
  have : verticalHallway = {q : ℝ² | 0 ≤ q 0 ∧ q 0 ≤ 1 ∧ q 1 ≤ 1} := by
    ext q; exact mem_verticalHallway_iff q
  rw [this]
  exact (isClosed_le continuous_const (continuous_coord 0)).inter
    ((isClosed_le (continuous_coord 0) continuous_const).inter
      (isClosed_le (continuous_coord 1) continuous_const))

lemma isClosed_gerversSofa : IsClosed gerversSofa :=
  ((isClosed_rotateTranslate_image _ _ isClosed_horizontalHallway).inter
    (isClosed_rotateTranslate_image _ _ isClosed_verticalHallway)).inter
    (isClosed_biInter fun _ _ => isClosed_rotateTranslate_image _ _ isClosed_hallway)

/-- **Gerver's sofa is a moving sofa, given that it is connected** (upstream
`isMovingSofa_gerversSofa`, modulo connectedness): the motion is `gmotion`. -/
theorem isMovingSofa_gerversSofa_of_isConnected (hc : IsConnected gerversSofa) :
    IsMovingSofa gerversSofa gmotion where
  isConnected := hc
  isClosed := isClosed_gerversSofa
  continuous := continuous_gmotion
  zero := gmotion_zero
  initial := by
    intro z hz
    obtain ⟨⟨⟨w, hw, rfl⟩, -⟩, -⟩ := hz
    rw [p_zero]
    have : rotateTranslate (0 : Real.Angle) 0 w = w := by
      rw [← Real.Angle.coe_zero, rotateTranslate_apply_eq_rot, add_zero, rot_zero]
    rwa [this]
  subset_hallway := by
    rintro τ _ ⟨z, hz, rfl⟩
    have hz' := hz.2
    simp only [mem_iInter₂] at hz'
    obtain ⟨w, hw, rfl⟩ := hz' (ang τ) (ang_mem τ)
    rw [gmotion, AffineIsometryEquiv.symm_apply_apply]
    exact hw
  final := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨⟨-, ⟨w, hw, rfl⟩⟩, -⟩ := hz
    have h1 : ang 1 = π / 2 := by simp [ang]
    rw [gmotion, h1, AffineIsometryEquiv.symm_apply_apply]
    exact hw

end Sofa.GP
