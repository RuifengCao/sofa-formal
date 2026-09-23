/-
# Sofa/RotationBound.lean — Baek Theorem 1.5.1 (after Gerver, p. 271)

A moving sofa of area `≥ 2.2` admits a movement whose rotation angle lies in
`[sec⁻¹ 2.2, π/2] = [arccos (5/11), π/2]`.

Proof (Baek p. 14): take the rotation angle `ω = -θ(1)` of the given movement.
(i) `ω ≤ -π/4`: at the moment of counter-clockwise rotation `π/4` every horizontal slice of the
sofa has length `≤ √2`, so `|S| ≤ √2`.
(ii) `|ω| < sec⁻¹ 2.2`: the final position puts `S` in a parallelogram of area `sec ω < 2.2`.
(iii) `ω > π/2`: stop at the first moment of clockwise rotation `π/2` and slide the sofa to the
right until it touches `x = 1`; it then lies in `V_L`.

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 1 (2026-09-17, Opus 5), no `sorry`.
-/
import Sofa.Monotone
import Sofa.Motion

noncomputable section

open Real Set MovingSofa MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace unitInterval ENNReal

namespace Sofa

/-! ## Areas of sets with short horizontal slices -/

/-- `{(x, y) : 0 ≤ y ≤ 1, D y ≤ x ≤ D y + ℓ}`. -/
def sliceRegion (D : ℝ → ℝ) (ℓ : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ D p.2 ≤ p.1 ∧ p.1 ≤ D p.2 + ℓ}

lemma measurableSet_sliceRegion {D : ℝ → ℝ} (hD : Measurable D) (ℓ : ℝ) :
    MeasurableSet (sliceRegion D ℓ) := by
  unfold sliceRegion
  simp only [Set.ofPred_and]
  exact (measurableSet_le measurable_const measurable_snd).inter
    ((measurableSet_le measurable_snd measurable_const).inter
      ((measurableSet_le (hD.comp measurable_snd) measurable_fst).inter
        (measurableSet_le measurable_fst ((hD.comp measurable_snd).add_const ℓ))))

lemma volume_sliceRegion_le {D : ℝ → ℝ} (hD : Measurable D) {ℓ : ℝ} :
    volume (sliceRegion D ℓ) ≤ ENNReal.ofReal ℓ := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (measurableSet_sliceRegion hD ℓ)]
  calc ∫⁻ y, volume ((fun x => (x, y)) ⁻¹' sliceRegion D ℓ)
      ≤ ∫⁻ y, (Set.Icc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal ℓ) y := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
        · rw [Set.indicator_of_mem hy]
          calc volume ((fun x => (x, y)) ⁻¹' sliceRegion D ℓ)
              ≤ volume (Set.Icc (D y) (D y + ℓ)) := by
                apply measure_mono
                intro x hx
                exact ⟨hx.2.2.1, hx.2.2.2⟩
            _ = ENNReal.ofReal ℓ := by
                rw [Real.volume_Icc]; congr 1; ring
        · have hempty : (fun x => (x, y)) ⁻¹' sliceRegion D ℓ = ∅ := by
            apply Set.eq_empty_of_forall_notMem
            intro x hx
            exact hy ⟨hx.1, hx.2.1⟩
          calc volume ((fun x => (x, y)) ⁻¹' sliceRegion D ℓ) = 0 := by
                rw [hempty, measure_empty]
            _ ≤ _ := zero_le
    _ = ENNReal.ofReal ℓ := by
        rw [lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc]
        simp

/-- If every point of `S` has height in `[0, 1]` and abscissa in `[D y, D y + ℓ]`, then
`|S| ≤ ℓ`. -/
lemma volume_le_of_slices (S : Set ℝ²) {D : ℝ → ℝ} {ℓ : ℝ} (hD : Measurable D)
    (hS : ∀ q ∈ S, 0 ≤ q 1 ∧ q 1 ≤ 1 ∧ D (q 1) ≤ q 0 ∧ q 0 ≤ D (q 1) + ℓ) :
    volume S ≤ ENNReal.ofReal ℓ := by
  calc volume S
      ≤ volume ((WithLp.ofLp : ℝ² → (Fin 2 → ℝ)) ⁻¹'
          (MeasurableEquiv.finTwoArrow ⁻¹' sliceRegion D ℓ)) := by
        apply measure_mono
        intro q hq
        exact hS q hq
    _ ≤ volume (MeasurableEquiv.finTwoArrow ⁻¹' sliceRegion D ℓ) :=
        (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage_le _
    _ ≤ volume (sliceRegion D ℓ) :=
        (volume_preserving_finTwoArrow ℝ).measure_preimage_le _
    _ ≤ ENNReal.ofReal ℓ := volume_sliceRegion_le hD

/-! ## Numerical facts about `sec⁻¹ 2.2 = arccos (5/11)` -/

lemma sqrt_two_mul_self : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)

lemma sqrt_two_gt : (1.4 : ℝ) < √2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

lemma sqrt_two_lt : √2 < (1.5 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma pi_div_four_lt_arccos : π / 4 < arccos (5 / 11) := by
  by_contra h
  push Not at h
  have h1 := cos_le_cos_of_nonneg_of_le_pi (arccos_nonneg _) (by linarith [pi_pos]) h
  rw [cos_arccos (by norm_num) (by norm_num), cos_pi_div_four] at h1
  linarith [sqrt_two_gt]

lemma arccos_lt_pi_div_two' : arccos (5 / 11) < π / 2 :=
  arccos_lt_pi_div_two.2 (by norm_num)

/-! ## Theorem 1.5.1 -/

lemma pt_add_smul_e₀ (a b d : ℝ) : pt a b + d • e₀ = pt (a + d) b := by
  ext i; fin_cases i <;> simp [pt, e₀, e₁]

/-- Sliding a point of `L` to the right keeps it in `L` as long as it stays left of `x = 1`. -/
lemma add_smul_e₀_mem_hallway {w : ℝ²} (hw : w ∈ hallway) {s : ℝ} (hs : 0 ≤ s)
    (h1 : w 0 + s ≤ 1) : w + s • e₀ ∈ hallway := by
  have e0 : (w + s • e₀) 0 = w 0 + s := by simp [e₀]
  have e1 : (w + s • e₀) 1 = w 1 := by simp [e₀]
  rw [hallway_eq_diff] at hw ⊢
  obtain ⟨⟨hx, hy⟩, hn⟩ := hw
  refine ⟨⟨by rw [e0]; exact h1, by rw [e1]; exact hy⟩, fun hm => hn ⟨?_, ?_⟩⟩
  · have := hm.1; rw [e0] at this; linarith
  · have := hm.2; rw [e1] at this; exact this

/-- **Theorem 1.5.1** (Gerver; Baek's modification).  A moving sofa of area `≥ 2.2` admits a
movement with rotation angle in `[sec⁻¹ 2.2, π/2]`. -/
theorem exists_rotationAngle_mem_of_volume_ge {s : Set ℝ²} {m : I → E(2)}
    (hm : IsMovingSofa s m) (hvol : ENNReal.ofReal 2.2 ≤ volume s) :
    ∃ (m' : I → E(2)) (θ' : I → ℝ), IsMovingSofa s m' ∧ Continuous θ' ∧ θ' 0 = 0 ∧
      (∀ t p, m' t p = rot (θ' t) p + m' t 0) ∧
      arccos (5 / 11) ≤ -θ' 1 ∧ -θ' 1 ≤ π / 2 := by
  obtain ⟨θ, hθc, hθ0, hθ⟩ := exists_rotationAngle hm.continuous hm.zero
  have hS : ∀ q ∈ s, 0 ≤ q 1 ∧ q 1 ≤ 1 := fun q hq =>
    ((mem_horizontalHallway_iff q).1 (hm.initial hq)).2
  -- a volume bound `< 2.2` is contradictory
  have hsmall : ∀ x : ℝ, x < 2.2 → volume s ≤ ENNReal.ofReal x → False := by
    intro x hx hle
    rcases ENNReal.ofReal_le_ofReal_iff'.1 (hvol.trans hle) with h | h
    · linarith
    · norm_num at h
  -- (i) the sofa never turns counter-clockwise by `π/4`
  have hi : θ 1 < π / 4 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨τ, hτ⟩ : ∃ τ : I, θ τ = π / 4 :=
      intermediate_value_univ 0 1 hθc ⟨by rw [hθ0]; positivity, hcon⟩
    have key : ∀ q ∈ s, 0 ≤ q 1 ∧ q 1 ≤ 1 ∧
        min (q 1 - √2 * (m τ 0) 0) (-q 1 - √2 * (m τ 0) 1) ≤ q 0 ∧
        q 0 ≤ min (q 1 - √2 * (m τ 0) 0) (-q 1 - √2 * (m τ 0) 1) + √2 := by
      intro q hq
      have hL := hm.subset_hallway τ ⟨q, hq, rfl⟩
      rw [hθ, hτ, hallway_eq_diff] at hL
      obtain ⟨⟨hx, hy⟩, hn⟩ := hL
      have hn' : ¬ (√2 / 2 * q 0 - √2 / 2 * q 1 + (m τ 0) 0 < 0 ∧
          √2 / 2 * q 0 + √2 / 2 * q 1 + (m τ 0) 1 < 0) := by
        intro h
        apply hn
        simp only [Qminus, mem_ofPred_eq, PiLp.add_apply, rot_coord_zero, rot_coord_one,
          cos_pi_div_four, sin_pi_div_four]
        exact h
      simp only [PiLp.add_apply, rot_coord_zero, rot_coord_one, cos_pi_div_four,
        sin_pi_div_four] at hx hy
      have h2 := sqrt_two_mul_self
      have e0 : q 0 = (q 1 - √2 * (m τ 0) 0)
          + √2 * (√2 / 2 * q 0 - √2 / 2 * q 1 + (m τ 0) 0) := by
        linear_combination (-(q 0 - q 1) / 2) * h2
      have e1 : q 0 = (-q 1 - √2 * (m τ 0) 1)
          + √2 * (√2 / 2 * q 0 + √2 / 2 * q 1 + (m τ 0) 1) := by
        linear_combination (-(q 0 + q 1) / 2) * h2
      have hs2 : 0 < √2 := by positivity
      refine ⟨(hS q hq).1, (hS q hq).2, ?_, ?_⟩
      · by_contra hlt
        push Not at hlt
        have hA := lt_of_lt_of_le hlt (min_le_left _ _)
        have hB := lt_of_lt_of_le hlt (min_le_right _ _)
        apply hn'
        constructor
        · by_contra h0
          push Not at h0
          have := mul_nonneg hs2.le h0
          linarith
        · by_contra h0
          push Not at h0
          have := mul_nonneg hs2.le h0
          linarith
      · have ha : q 0 ≤ (q 1 - √2 * (m τ 0) 0) + √2 := by
          have := mul_le_mul_of_nonneg_left hx hs2.le
          linarith
        have hb : q 0 ≤ (-q 1 - √2 * (m τ 0) 1) + √2 := by
          have := mul_le_mul_of_nonneg_left hy hs2.le
          linarith
        rw [← min_add_add_right]
        exact le_min ha hb
    have hvol' := volume_le_of_slices s
      (D := fun y => min (y - √2 * (m τ 0) 0) (-y - √2 * (m τ 0) 1))
      (by fun_prop) key
    exact hsmall (√2) (by linarith [sqrt_two_lt]) hvol'
  -- (ii) the final rotation is not small
  have hii : ¬ |θ 1| < arccos (5 / 11) := by
    intro hlt
    have hcos : 5 / 11 < cos (θ 1) := by
      rw [← cos_abs]
      have := cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _)
        (by linarith [arccos_lt_pi_div_two', pi_pos]) hlt
      rwa [cos_arccos (by norm_num) (by norm_num)] at this
    have hfin : ∀ q ∈ s, -(m 1 0) 0 ≤ cos (θ 1) * q 0 + (-sin (θ 1)) * q 1 ∧
        cos (θ 1) * q 0 + (-sin (θ 1)) * q 1 ≤ -(m 1 0) 0 + 1 := by
      intro q hq
      have h := (mem_verticalHallway_iff (m 1 q)).1 (hm.final ⟨q, hq, rfl⟩)
      rw [hθ, PiLp.add_apply, rot_coord_zero] at h
      constructor <;> linarith [h.1, h.2.1]
    have hvol' := volume_le_of_forall_mem_strip s (cos (θ 1)) (-sin (θ 1)) (-(m 1 0) 0)
      (by linarith) hfin hS
    rw [abs_of_pos (by linarith)] at hvol'
    refine hsmall (1 / cos (θ 1)) ?_ hvol'
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  have hω : arccos (5 / 11) ≤ -θ 1 := by
    rw [not_lt] at hii
    rcases le_total 0 (θ 1) with h | h
    · rw [abs_of_nonneg h] at hii
      linarith [pi_div_four_lt_arccos]
    · rw [abs_of_nonpos h] at hii
      exact hii
  by_cases hω2 : -θ 1 ≤ π / 2
  · exact ⟨m, θ, hm, hθc, hθ0, hθ, hω, hω2⟩
  -- (iii) stop at clockwise rotation `π/2` and slide right
  push Not at hω2
  obtain ⟨τ₂, hτ₂⟩ : ∃ τ : I, θ τ = -(π / 2) :=
    intermediate_value_univ 1 0 hθc ⟨by linarith, by rw [hθ0]; linarith [pi_pos]⟩
  set c := m τ₂ 0 with hc
  have hS2 : ∀ q ∈ s, m τ₂ q = pt (q 1 + c 0) (-q 0 + c 1) := by
    intro q hq
    rw [hθ, hτ₂]
    ext i; fin_cases i <;> simp [cos_neg, sin_neg, pt, e₀, e₁, c]
  have hne := hm.nonempty
  have hcpt := hm.isCompact
  obtain ⟨qtop, hqtop, hqtop1⟩ := exists_supportFn_eq hcpt hne (π / 2)
  rw [inner_u_pi_div_two] at hqtop1
  have hxle : ∀ q ∈ s, q 1 + c 0 ≤ 1 := by
    intro q hq
    have hL := hm.subset_hallway τ₂ ⟨q, hq, rfl⟩
    rw [hS2 q hq, hallway_eq_diff] at hL
    have := hL.1.1
    rwa [pt_zero] at this
  set δ := 1 - c 0 - supportFn s (π / 2) with hδ
  have hδ0 : 0 ≤ δ := by
    have := hxle qtop hqtop
    rw [hqtop1] at this
    linarith
  have hq1 : ∀ q ∈ s, q 1 ≤ supportFn s (π / 2) := fun q hq => by
    have := le_supportFn hcpt hq (π / 2)
    rwa [inner_u_pi_div_two] at this
  -- the re-parametrised motion
  let rp : I → I := fun τ => ⟨min 1 (2 * (τ : ℝ)) * (τ₂ : ℝ), by
    have h1 : 0 ≤ min 1 (2 * (τ : ℝ)) := le_min zero_le_one (by linarith [τ.2.1])
    have h2 : min 1 (2 * (τ : ℝ)) ≤ 1 := min_le_left _ _
    exact ⟨mul_nonneg h1 τ₂.2.1, mul_le_one₀ h2 τ₂.2.1 τ₂.2.2⟩⟩
  have hrpc : Continuous rp := by
    apply Continuous.subtype_mk
    fun_prop
  have hrp0 : rp 0 = 0 := by ext; simp [rp]
  have hrp1 : rp 1 = τ₂ := by ext; simp [rp]
  let sh : I → ℝ := fun τ => δ * max 0 (2 * (τ : ℝ) - 1)
  have hsh0 : ∀ τ, 0 ≤ sh τ := fun τ => mul_nonneg hδ0 (le_max_left _ _)
  have hshδ : ∀ τ, sh τ ≤ δ := fun τ => by
    have : max 0 (2 * (τ : ℝ) - 1) ≤ 1 := max_le zero_le_one (by linarith [τ.2.2])
    exact mul_le_of_le_one_right hδ0 this
  have hshrp : ∀ τ, 0 < sh τ → rp τ = τ₂ := by
    intro τ hpos
    have : 1 / 2 < (τ : ℝ) := by
      by_contra hle
      push Not at hle
      have : max 0 (2 * (τ : ℝ) - 1) = 0 := max_eq_left (by linarith)
      simp only [sh, this, mul_zero, lt_self_iff_false] at hpos
    ext
    simp only [rp]
    rw [min_eq_left (by linarith), one_mul]
  let m' : I → E(2) := fun τ =>
    (m (rp τ)).trans (AffineIsometryEquiv.vaddConst ℝ (sh τ • e₀))
  have hm'app : ∀ τ q, m' τ q = m (rp τ) q + sh τ • e₀ := by
    intro τ q
    simp only [m', AffineIsometryEquiv.coe_trans, Function.comp_apply,
      AffineIsometryEquiv.coe_vaddConst, vadd_eq_add]
  have hsh1 : sh 1 = δ := by simp [sh]; norm_num
  refine ⟨m', fun τ => θ (rp τ), ⟨hm.isConnected, hm.isClosed, ?_, ?_, hm.initial, ?_, ?_⟩,
    hθc.comp hrpc, by simp only [hrp0, hθ0], ?_, ?_, ?_⟩
  · refine continuous_motion_of_continuous_apply fun q => ?_
    simp only [hm'app]
    exact ((continuous_eval q).comp (hm.continuous.comp hrpc)).add
      ((continuous_const.mul (continuous_const.max
        ((continuous_const.mul continuous_subtype_val).sub continuous_const))).smul
        continuous_const)
  · ext q : 1
    rw [hm'app, hrp0, hm.zero]
    simp [sh]
  · rintro τ _ ⟨q, hq, rfl⟩
    rw [hm'app]
    rcases (hsh0 τ).lt_or_eq with hpos | hzero
    · rw [hshrp τ hpos]
      refine add_smul_e₀_mem_hallway (hm.subset_hallway τ₂ ⟨q, hq, rfl⟩) (hsh0 τ) ?_
      rw [hS2 q hq, pt_zero]
      linarith [hq1 q hq, hshδ τ]
    · rw [← hzero, zero_smul, add_zero]
      exact hm.subset_hallway _ ⟨q, hq, rfl⟩
  · rintro _ ⟨q, hq, rfl⟩
    rw [hm'app, hrp1, hsh1, hS2 q hq, pt_add_smul_e₀]
    have hL := hm.subset_hallway τ₂ ⟨q, hq, rfl⟩
    rw [hS2 q hq, hallway_eq_diff] at hL
    have hy := hL.1.2
    rw [pt_one] at hy
    have htop : qtop 1 ≤ 1 := (hS qtop hqtop).2
    rw [hqtop1] at htop
    rw [mem_verticalHallway_iff, pt_zero, pt_one]
    refine ⟨?_, ?_, hy⟩
    · have := (hS q hq).1
      rw [hδ]; linarith
    · have := hq1 q hq
      rw [hδ]; linarith
  · intro τ p
    show m' τ p = rot (θ (rp τ)) p + m' τ 0
    rw [hm'app, hm'app, hθ (rp τ) p]
    abel
  · show arccos (5 / 11) ≤ -θ (rp 1)
    rw [hrp1, hτ₂, neg_neg]
    exact le_of_lt arccos_lt_pi_div_two'
  · show -θ (rp 1) ≤ π / 2
    rw [hrp1, hτ₂, neg_neg]

end Sofa
