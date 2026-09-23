/-
# Sofa/AbsCont.lean — absolute continuity of `σ_K`, and Theorem 6.1.1

Clause (1) of Baek's Definition 6.1.2 asks for densities `r_K, s_K` with `σ_K = r_K dt` on
`[0, π/2)` and `σ_K = s_K(· − π/2) dt` on `(π/2, π]`; by the Radon–Nikodym theorem this is
exactly `σ_K ≪ dt` there.

Theorem 6.4.3 gives the Lipschitz bound `arcFn K b − arcFn K a ≤ (1+2R)(b − a)` on `[0, π/2)`,
and the general principle is:

> if the Stieltjes function `f` is `C`-Lipschitz on `[lo, hi]`, then its measure restricted to
> `(lo, hi]` is `≤ C · volume`, hence absolutely continuous.

The proof is by a *difference Stieltjes function*: with `A(t) := f(clamp t)` and
`D(t) := C·t − A(t)`, the Lipschitz bound says `D` is monotone, so `D` is a Stieltjes function
too, and `A.measure + D.measure` agrees with `C • volume` on every `Ioc` — hence they are equal
(`Measure.ext_of_Ioc'`), and `A.measure ≤ C • volume`.

STATUS: [PROOF-C-local] round 1 (2026-09-22, Opus 5).
-/
import Sofa.ArmPairK

noncomputable section

open Real Set Filter Topology MeasureTheory Metric
open scoped EuclideanGeometry RealInnerProductSpace ENNReal

namespace Sofa

variable {K : Set ℝ²}

/-! ## The clamp -/

lemma clamp_le_clamp {lo hi : ℝ} {a b : ℝ} (hab : a ≤ b) :
    max lo (min a hi) ≤ max lo (min b hi) :=
  max_le_max le_rfl (min_le_min hab le_rfl)

lemma clamp_sub_le {lo hi : ℝ} {a b : ℝ} (hab : a ≤ b) :
    max lo (min b hi) - max lo (min a hi) ≤ b - a := by
  have hmin : min b hi ≤ min a hi + (b - a) := by
    rcases min_cases a hi with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e]
    · exact le_trans (min_le_left _ _) (by linarith)
    · exact le_trans (min_le_right _ _) (by linarith)
  have hmono : min a hi ≤ min b hi := min_le_min hab le_rfl
  have hmax : max lo (min b hi) ≤ max lo (min a hi) + (min b hi - min a hi) := by
    rcases max_cases lo (min a hi) with ⟨e, hle⟩ | ⟨e, hle⟩ <;> rw [e]
    · exact max_le (by linarith) (by linarith)
    · exact max_le (by linarith) (by linarith)
  linarith

lemma clamp_mem_Icc {lo hi : ℝ} (hlohi : lo ≤ hi) (t : ℝ) :
    max lo (min t hi) ∈ Icc lo hi :=
  ⟨le_max_left _ _, max_le hlohi (min_le_right _ _)⟩

/-! ## The two Stieltjes functions -/

/-- `arcFn K` with the argument clamped to `[lo, hi]`. -/
def clampSF (hK : IsCompact K) (hne : K.Nonempty) (lo hi : ℝ) : StieltjesFunction ℝ where
  toFun := fun t => arcFn K (max lo (min t hi))
  mono' := fun _ _ hab => arcFn_mono hK hne (clamp_le_clamp hab)
  right_continuous' := by
    intro x
    have hclamp : ContinuousWithinAt (fun t : ℝ => max lo (min t hi)) (Ici x) x :=
      (continuous_const.max (continuous_id.min continuous_const)).continuousWithinAt
    have hmaps : MapsTo (fun t : ℝ => max lo (min t hi)) (Ici x) (Ici (max lo (min x hi))) :=
      fun _ hy => clamp_le_clamp hy
    exact (arcFn_right_continuous hK hne _).comp hclamp hmaps

@[simp] lemma clampSF_apply (hK : IsCompact K) (hne : K.Nonempty) (lo hi t : ℝ) :
    clampSF hK hne lo hi t = arcFn K (max lo (min t hi)) := rfl

/-- `C·t − arcFn K (clamp t)`: monotone exactly because `arcFn K` is `C`-Lipschitz on
`[lo, hi]`. -/
def lipDiffSF (hK : IsCompact K) (hne : K.Nonempty) {lo hi C : ℝ} (hlohi : lo ≤ hi) (hC : 0 ≤ C)
    (hlip : ∀ a b : ℝ, lo ≤ a → a ≤ b → b ≤ hi → arcFn K b - arcFn K a ≤ C * (b - a)) :
    StieltjesFunction ℝ where
  toFun := fun t => C * t - arcFn K (max lo (min t hi))
  mono' := by
    intro a b hab
    have hca := clamp_mem_Icc hlohi a
    have hcb := clamp_mem_Icc hlohi b
    have hmono := clamp_le_clamp (lo := lo) (hi := hi) hab
    have h1 := hlip _ _ hca.1 hmono hcb.2
    have h2 := clamp_sub_le (lo := lo) (hi := hi) hab
    have h3 : C * (max lo (min b hi) - max lo (min a hi)) ≤ C * (b - a) :=
      mul_le_mul_of_nonneg_left h2 hC
    simp only
    linarith
  right_continuous' := by
    intro x
    have hclamp : ContinuousWithinAt (fun t : ℝ => max lo (min t hi)) (Ici x) x :=
      (continuous_const.max (continuous_id.min continuous_const)).continuousWithinAt
    have hmaps : MapsTo (fun t : ℝ => max lo (min t hi)) (Ici x) (Ici (max lo (min x hi))) :=
      fun _ hy => clamp_le_clamp hy
    exact (continuous_const.mul continuous_id).continuousWithinAt.sub
      ((arcFn_right_continuous hK hne _).comp hclamp hmaps)

/-! ## `clampSF.measure ≤ C • volume` -/

theorem clampSF_measure_le (hK : IsCompact K) (hne : K.Nonempty) {lo hi C : ℝ}
    (hlohi : lo ≤ hi) (hC : 0 ≤ C)
    (hlip : ∀ a b : ℝ, lo ≤ a → a ≤ b → b ≤ hi → arcFn K b - arcFn K a ≤ C * (b - a)) :
    (clampSF hK hne lo hi).measure ≤ ENNReal.ofReal C • volume := by
  set A := clampSF hK hne lo hi with hA
  set D := lipDiffSF hK hne hlohi hC hlip with hD
  have hsum : A.measure + D.measure = ENNReal.ofReal C • volume := by
    refine Measure.ext_of_Ioc' _ _ (fun a b _ => ?_) (fun a b hab => ?_)
    · rw [Measure.coe_add, Pi.add_apply, A.measure_Ioc, D.measure_Ioc]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
    · have hAv : A.measure (Ioc a b) = ENNReal.ofReal (A b - A a) := A.measure_Ioc a b
      have hDv : D.measure (Ioc a b) = ENNReal.ofReal (D b - D a) := D.measure_Ioc a b
      have hA0 : 0 ≤ A b - A a := sub_nonneg.2 (A.mono hab.le)
      have hD0 : 0 ≤ D b - D a := sub_nonneg.2 (D.mono hab.le)
      have hsum' : (A b - A a) + (D b - D a) = C * (b - a) := by
        simp only [hA, hD, clampSF, lipDiffSF]
        ring
      rw [Measure.coe_add, Pi.add_apply, hAv, hDv, ← ENNReal.ofReal_add hA0 hD0, hsum',
        Measure.smul_apply, smul_eq_mul, Real.volume_Ioc, ← ENNReal.ofReal_mul hC]
  calc A.measure ≤ A.measure + D.measure := Measure.le_add_right le_rfl
    _ = ENNReal.ofReal C • volume := hsum

/-! ## `σ_K` restricted to `(lo, hi]` -/

/-- On `(lo, hi]` the measure of `arcFn K` agrees with the measure of the clamped version:
clamping changes nothing inside the window, and outside it both sides are `0`. -/
theorem sigmaK_restrict_eq_clampSF (hK : IsCompact K) (hne : K.Nonempty) (lo hi : ℝ) :
    (sigmaK K).restrict (Ioc lo hi) = (clampSF hK hne lo hi).measure.restrict (Ioc lo hi) := by
  have key : ∀ ⦃a b : ℝ⦄, a < b →
      (sigmaK K).restrict (Ioc lo hi) (Ioc a b)
        = (clampSF hK hne lo hi).measure.restrict (Ioc lo hi) (Ioc a b) := by
    intro a b _
    rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
      Set.Ioc_inter_Ioc, sigmaK_Ioc hK hne, StieltjesFunction.measure_Ioc]
    rcases lt_or_ge (a ⊔ lo) (b ⊓ hi) with h | h
    · have hlo : lo ≤ b ⊓ hi := le_trans le_sup_right h.le
      have hhi : a ⊔ lo ≤ hi := le_trans h.le inf_le_right
      have h1 : max lo (min (b ⊓ hi) hi) = b ⊓ hi := by
        rw [min_eq_left inf_le_right, max_eq_right hlo]
      have h2 : max lo (min (a ⊔ lo) hi) = a ⊔ lo := by
        rw [min_eq_left hhi, max_eq_right le_sup_right]
      rw [clampSF_apply, clampSF_apply, h1, h2]
    · have e1 : arcFn K (b ⊓ hi) - arcFn K (a ⊔ lo) ≤ 0 := by
        linarith [arcFn_mono hK hne h]
      have e2 : clampSF hK hne lo hi (b ⊓ hi) - clampSF hK hne lo hi (a ⊔ lo) ≤ 0 := by
        linarith [(clampSF hK hne lo hi).mono h]
      rw [ENNReal.ofReal_eq_zero.2 e1, ENNReal.ofReal_eq_zero.2 e2]
  refine Measure.ext_of_Ioc' _ _ (fun a b _ => ?_) key
  rw [Measure.restrict_apply measurableSet_Ioc, Set.Ioc_inter_Ioc, sigmaK_Ioc hK hne]
  exact ENNReal.ofReal_ne_top

/-- **The Lipschitz ⇒ absolutely continuous principle.**  If `arcFn K` is `C`-Lipschitz on
`[lo, hi]` then `σ_K` restricted to `(lo, hi]` is absolutely continuous. -/
theorem sigmaK_restrict_ac (hK : IsCompact K) (hne : K.Nonempty) {lo hi C : ℝ}
    (hlohi : lo ≤ hi) (hC : 0 ≤ C)
    (hlip : ∀ a b : ℝ, lo ≤ a → a ≤ b → b ≤ hi → arcFn K b - arcFn K a ≤ C * (b - a)) :
    (sigmaK K).restrict (Ioc lo hi) ≪ volume := by
  refine Measure.absolutelyContinuous_of_le_smul (c := ENNReal.ofReal C) ?_
  rw [sigmaK_restrict_eq_clampSF hK hne]
  exact le_trans Measure.restrict_le_self (clampSF_measure_le hK hne hlohi hC hlip)

/-! ## The Lipschitz bound on `[0, π/2)` -/

/-- **Theorem 6.4.3 ⇒ Lipschitz.**  For a balanced maximum cap,
`arcFn K b − arcFn K a ≤ (1 + 2R)(b − a)` whenever `0 ≤ a ≤ b < π/2`. -/
theorem arcFn_lip_left (hK : IsBalancedMaxCap K (π / 2)) {R : ℝ}
    (hR : ∀ p ∈ K, ‖p‖ ≤ R) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < π / 2) :
    arcFn K b - arcFn K a ≤ (1 + 2 * R) * (b - a) := by
  have hKc := hK.1.isCompact
  have hKne := hK.1.nonempty
  -- Theorem 6.4.3
  have key : (sigmaK K (Ioc a b)).toReal ≤ ∫ t in a..b, k0 (armGp K t) := by
    rcases eq_or_lt_of_le ha with h0 | h0
    · rcases eq_or_lt_of_le hab with he | hlt
      · rw [← he, ← h0]
        simp
      · rw [← h0]
        exact sigmaK_Ioc_zero_le_integral' hK (by linarith) hb
    · exact sigmaK_Ioc_le_integral_balanced' hK h0 hab hb
  -- the integrand is bounded by `1 + 2R`
  have hint : IntervalIntegrable (fun t => k0 (armGp K t)) volume a b :=
    intervalIntegrable_k0_comp (intervalIntegrable_armGp hKc hKne a b)
  have hpt : ∀ t ∈ Icc a b, k0 (armGp K t) ≤ 1 + 2 * R := fun t _ =>
    (k0_le_one_add_abs _).trans (by linarith [abs_armGp_le hKc hKne hR t])
  have hbd : (∫ t in a..b, k0 (armGp K t)) ≤ (b - a) * (1 + 2 * R) := by
    have h2 := intervalIntegral.integral_mono_on hab hint
      (intervalIntegrable_const (c := 1 + 2 * R)) hpt
    rwa [intervalIntegral.integral_const, smul_eq_mul] at h2
  -- and `σ_K((a,b]) = arcFn K b − arcFn K a`
  have harc : (sigmaK K (Ioc a b)).toReal = arcFn K b - arcFn K a := by
    rw [sigmaK_Ioc hKc hKne, ENNReal.toReal_ofReal (by linarith [arcFn_mono hKc hKne hab])]
  rw [harc] at key
  linarith [hbd, mul_comm (b - a) (1 + 2 * R)]

/-! ## Absolute continuity on `[0, π/2)` -/

/-- `σ_K` restricted to `(0, c]` is absolutely continuous for every `c < π/2`. -/
theorem sigmaK_restrict_ac_left (hK : IsBalancedMaxCap K (π / 2)) {c : ℝ}
    (hc0 : 0 ≤ c) (hc2 : c < π / 2) :
    (sigmaK K).restrict (Ioc 0 c) ≪ volume := by
  obtain ⟨R, hR0, hR⟩ := exists_radius hK.1.isCompact hK.1.nonempty
  exact sigmaK_restrict_ac hK.1.isCompact hK.1.nonempty hc0 (by linarith)
    (fun a b ha hab hbc => arcFn_lip_left hK hR ha hab (lt_of_le_of_lt hbc hc2))

/-- **Def 6.1.2 (1), left half**: `σ_K` is absolutely continuous on `[0, π/2)`. -/
theorem sigmaK_ac_left (hK : IsBalancedMaxCap K (π / 2)) :
    (sigmaK K).restrict (Ico 0 (π / 2)) ≪ volume := by
  have hKc := hK.1.isCompact
  have hKne := hK.1.nonempty
  have hpi := pi_pos
  set c : ℕ → ℝ := fun n => π / 2 - 1 / (n + 1) with hc
  intro s hs
  rw [Measure.restrict_apply' measurableSet_Ico]
  -- `σ_K({0}) = 0` is the round-25 endpoint theorem
  have hzero : sigmaK K {(0 : ℝ)} = 0 := by
    rw [sigmaK_singleton hKc hKne, edgeLength_zero_of_balanced hK, ENNReal.ofReal_zero]
  have hcover : s ∩ Ico 0 (π / 2) ⊆ {(0 : ℝ)} ∪ ⋃ n : ℕ, (s ∩ Ioc 0 (c n)) := by
    rintro x ⟨hxs, hx0, hx2⟩
    rcases eq_or_lt_of_le hx0 with he | hlt
    · exact Or.inl (by simp [← he])
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < π / 2 - x by linarith)
      exact Or.inr (mem_iUnion.2 ⟨n, hxs, hlt, by simp only [hc]; linarith⟩)
  have hterm : ∀ n : ℕ, sigmaK K (s ∩ Ioc 0 (c n)) = 0 := by
    intro n
    have hc0 : (0:ℝ) ≤ c n := by
      simp only [hc]
      have h1 : (1:ℝ) / (n + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [Nat.cast_nonneg (α := ℝ) n]
      linarith [pi_gt_three]
    have hc2 : c n < π / 2 := by
      simp only [hc]
      have : (0:ℝ) < 1 / (n + 1) := by positivity
      linarith
    have hac := sigmaK_restrict_ac_left hK hc0 hc2 hs
    rwa [Measure.restrict_apply' measurableSet_Ioc] at hac
  refine le_antisymm ?_ bot_le
  calc sigmaK K (s ∩ Ico 0 (π / 2))
      ≤ sigmaK K ({(0:ℝ)} ∪ ⋃ n : ℕ, (s ∩ Ioc 0 (c n))) := measure_mono hcover
    _ ≤ sigmaK K {(0:ℝ)} + sigmaK K (⋃ n : ℕ, (s ∩ Ioc 0 (c n))) := measure_union_le _ _
    _ ≤ 0 + ∑' n : ℕ, sigmaK K (s ∩ Ioc 0 (c n)) := by
        rw [hzero]; exact add_le_add le_rfl (measure_iUnion_le _)
    _ = 0 := by simp [hterm]

/-! ## The mirror identity and the Lipschitz bound on `(π/2, π]` -/

/-- `arcFn` of the mirror image, in terms of `K`. -/
lemma arcFn_mirror_eq (K : Set ℝ²) (t : ℝ) :
    arcFn (mirror (π / 2) '' K) t
      = -edgeMin K (π - t) + ∫ r in (π - t)..π, supportFn K r := by
  rw [arcFn, inner_vtxP_v, edgeMax_mirror, show π / 2 + π / 2 - t = π - t by ring]
  congr 1
  have hcong : (∫ s in (0:ℝ)..t, supportFn (mirror (π / 2) '' K) s)
      = ∫ s in (0:ℝ)..t, supportFn K (π - s) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [supportFn_mirror, show π / 2 + π / 2 - s = π - s by ring]
  rw [hcong, intervalIntegral.integral_comp_sub_left (f := supportFn K) π, sub_zero]

/-- `σ_K` has no atom at `π` either. -/
theorem edgeLength_pi_of_balanced (hK : IsBalancedMaxCap K (π / 2)) : edgeLength K π = 0 := by
  have hpi := pi_pos
  have hM := hK.image_mirror_le (by linarith : (0:ℝ) < π / 2) le_rfl
  have h := edgeLength_zero_of_balanced hM
  rwa [edgeLength_mirror, show π / 2 + π / 2 - (0:ℝ) = π by ring] at h

/-- `e_K(t) = 0` on all of `(π/2, π]`, so `edgeMax K = edgeMin K` there. -/
theorem edgeMax_eq_edgeMin_upper (hK : IsBalancedMaxCap K (π / 2)) {t : ℝ}
    (ht0 : π / 2 < t) (ht : t ≤ π) : edgeMax K t = edgeMin K t := by
  have h : edgeLength K t = 0 := by
    rcases eq_or_lt_of_le ht with he | hlt
    · rw [he]; exact edgeLength_pi_of_balanced hK
    · exact edgeLength_eq_zero_of_balanced_upper hK ht0 hlt
  rw [edgeLength, sub_eq_zero] at h
  exact h

/-- **The mirror identity.**  On `(π/2, π]` the increment of `arcFn K` equals the increment of
`arcFn (K^m)` over the reflected interval in `[0, π/2)`. -/
theorem arcFn_sub_eq_mirror (hK : IsBalancedMaxCap K (π / 2)) {a b : ℝ}
    (ha : π / 2 < a) (hab : a ≤ b) (hb : b ≤ π) :
    arcFn K b - arcFn K a
      = arcFn (mirror (π / 2) '' K) (π - a) - arcFn (mirror (π / 2) '' K) (π - b) := by
  have hKc := hK.1.isCompact
  have hKne := hK.1.nonempty
  have hea := edgeMax_eq_edgeMin_upper hK ha (le_trans hab hb)
  have heb := edgeMax_eq_edgeMin_upper hK (lt_of_lt_of_le ha hab) hb
  have hadd1 : (∫ s in (0:ℝ)..a, supportFn K s) + ∫ s in a..b, supportFn K s
      = ∫ s in (0:ℝ)..b, supportFn K s :=
    intervalIntegral.integral_add_adjacent_intervals
      (integrable_supportFn hKc hKne 0 a) (integrable_supportFn hKc hKne a b)
  have hadd2 : (∫ s in a..b, supportFn K s) + ∫ s in b..π, supportFn K s
      = ∫ s in a..π, supportFn K s :=
    intervalIntegral.integral_add_adjacent_intervals
      (integrable_supportFn hKc hKne a b) (integrable_supportFn hKc hKne b π)
  rw [arcFn_mirror_eq, arcFn_mirror_eq, show π - (π - a) = a by ring,
    show π - (π - b) = b by ring, arcFn, arcFn, inner_vtxP_v, inner_vtxP_v, hea, heb]
  linarith

/-- **The Lipschitz bound on `(π/2, π]`.** -/
theorem arcFn_lip_right (hK : IsBalancedMaxCap K (π / 2)) {R : ℝ}
    (hR : ∀ p ∈ K, ‖p‖ ≤ R) {a b : ℝ} (ha : π / 2 < a) (hab : a ≤ b) (hb : b ≤ π) :
    arcFn K b - arcFn K a ≤ (1 + 2 * R) * (b - a) := by
  have hpi := pi_pos
  have hM := hK.image_mirror_le (by linarith : (0:ℝ) < π / 2) le_rfl
  have hRM : ∀ p ∈ mirror (π / 2) '' K, ‖p‖ ≤ R := by
    rintro _ ⟨q, hq, rfl⟩
    have hnorm : ‖mirror (π / 2) q‖ = ‖q‖ := by
      rw [← coe_mirrorL]; exact (mirrorL (π / 2)).norm_map q
    rw [hnorm]; exact hR q hq
  have h := arcFn_lip_left hM hRM (a := π - b) (b := π - a)
    (by linarith) (by linarith) (by linarith)
  rw [arcFn_sub_eq_mirror hK ha hab hb]
  calc arcFn (mirror (π / 2) '' K) (π - a) - arcFn (mirror (π / 2) '' K) (π - b)
      ≤ (1 + 2 * R) * (π - a - (π - b)) := h
    _ = (1 + 2 * R) * (b - a) := by ring

/-- **Def 6.1.2 (1), right half**: `σ_K` is absolutely continuous on `(π/2, π]`. -/
theorem sigmaK_ac_right (hK : IsBalancedMaxCap K (π / 2)) :
    (sigmaK K).restrict (Ioc (π / 2) π) ≪ volume := by
  have hKc := hK.1.isCompact
  have hKne := hK.1.nonempty
  have hpi3 := pi_gt_three
  obtain ⟨R, hR0, hR⟩ := exists_radius hKc hKne
  set d : ℕ → ℝ := fun n => π / 2 + 1 / (n + 1) with hd
  have hdpi : ∀ n : ℕ, d n ≤ π := by
    intro n
    have h1 : (1:ℝ) / (n + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    simp only [hd]; linarith
  have hdlt : ∀ n : ℕ, π / 2 < d n := by
    intro n
    have : (0:ℝ) < 1 / (n + 1) := by positivity
    simp only [hd]; linarith
  intro s hs
  rw [Measure.restrict_apply' measurableSet_Ioc]
  have hterm : ∀ n : ℕ, sigmaK K (s ∩ Ioc (d n) π) = 0 := by
    intro n
    have hac : (sigmaK K).restrict (Ioc (d n) π) ≪ volume :=
      sigmaK_restrict_ac hKc hKne (hdpi n) (by linarith)
        (fun a b ha hab hbpi => arcFn_lip_right hK hR (lt_of_lt_of_le (hdlt n) ha) hab hbpi)
    have := hac hs
    rwa [Measure.restrict_apply' measurableSet_Ioc] at this
  have hcover : s ∩ Ioc (π / 2) π ⊆ ⋃ n : ℕ, (s ∩ Ioc (d n) π) := by
    rintro x ⟨hxs, hx0, hx2⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < x - π / 2 by linarith)
    exact mem_iUnion.2 ⟨n, hxs, by simp only [hd]; linarith, hx2⟩
  refine le_antisymm ?_ bot_le
  calc sigmaK K (s ∩ Ioc (π / 2) π)
      ≤ sigmaK K (⋃ n : ℕ, (s ∩ Ioc (d n) π)) := measure_mono hcover
    _ ≤ ∑' n : ℕ, sigmaK K (s ∩ Ioc (d n) π) := measure_iUnion_le _
    _ = 0 := by simp [hterm]

/-! ## Clause (1) in Baek's own words: the densities `r_K`, `s_K` -/

/-- Radon–Nikodym: absolute continuity is exactly the existence of a measurable density. -/
theorem exists_density_of_ac {μ : Measure ℝ} [SigmaFinite μ] (h : μ ≪ volume) :
    ∃ r : ℝ → ℝ≥0∞, Measurable r ∧ μ = volume.withDensity r :=
  ⟨μ.rnDeriv volume, μ.measurable_rnDeriv volume,
    (Measure.withDensity_rnDeriv_eq μ volume h).symm⟩

/-- **Def 6.1.2 (1) literally**: for a balanced maximum cap there are measurable densities
`r_K` on `[0, π/2)` and `s_K` on `(π/2, π]` with `σ_K = r_K dt` and `σ_K = s_K dt` there. -/
theorem exists_densities_of_balanced (hK : IsBalancedMaxCap K (π / 2)) :
    (∃ r : ℝ → ℝ≥0∞, Measurable r ∧
        (sigmaK K).restrict (Ico 0 (π / 2)) = volume.withDensity r) ∧
      ∃ s : ℝ → ℝ≥0∞, Measurable s ∧
        (sigmaK K).restrict (Ioc (π / 2) π) = volume.withDensity s :=
  ⟨exists_density_of_ac (sigmaK_ac_left hK), exists_density_of_ac (sigmaK_ac_right hK)⟩

/-! ## Theorem 6.1.1 -/

/-- **Baek Theorem 6.1.1**: every balanced maximum cap satisfies the injectivity condition.

* (1) is `sigmaK_ac_left` / `sigmaK_ac_right`, i.e. Theorem 6.4.3 (`Sofa/PolyGap.lean`) turned
  into a Lipschitz bound and then into absolute continuity, together with the endpoint theorem
  `edgeLength_zero_of_balanced` (`Sofa/EndPoint.lean`) which kills the only possible atom of the
  left half, and its mirror image which kills the atom at `π`.
* (2) is Proposition 6.4.6 (1) (`Sofa/ArmPairK.lean`).
* (3) is Theorem 6.5.6 (`Sofa/ArmPairK.lean`). -/
theorem isInjectiveCap_of_balanced (hK : IsBalancedMaxCap K (π / 2)) : IsInjectiveCap K where
  isCap := hK.1
  ac_left := sigmaK_ac_left hK
  ac_right := sigmaK_ac_right hK
  continuousOn_armFm := continuousOn_armFm_Icc hK
  continuousOn_armGp := continuousOn_armGp_Icc hK
  one_lt_arm := fun _ ht =>
    ⟨one_lt_armFp_of_balanced hK ht.1 ht.2, one_lt_armGp_of_balanced hK ht.1 ht.2⟩

end Sofa
