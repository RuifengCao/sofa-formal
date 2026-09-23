/-
# Sofa/CapHalf.lean — the shape of a cap with rotation angle `π/2`

For `ω = π/2` a cap `K` lies in the strip `0 ≤ y ≤ 1`, touches both lines, and is cut out by its
supporting half-planes with normals in `[0, π] ∪ {3π/2}`.  Chapter 8 (Lemma 8.3.5 and the
bookkeeping of Lemma 8.3.7) uses the following consequences, none of which is stated in the paper:

* projecting a point of `K` straight down to the floor stays in `K` (`proj_floor_mem`); hence the
  two floor corners `(h(0), 0)` and `(−h(π), 0)` are in `K` (`cornerR_mem`, `cornerL_mem`), the
  left face reaches the floor (`edgeMax_pi_of_isCap`, mirror of `edgeMin_zero_of_isCap`);
* between the left face and the floor the support function is that of the corner:
  `h(t) = −h(π) cos t` on `[π, 3π/2]` and `h(t) = h(0) cos t` on `[3π/2, 2π]`;
* **Lemma 8.3.5, core** (`volumeReal_cap`): `|K| = J(u^{0,π}_K) + ½h(π)|e_K(π)| + ½h(0)|e_K(0)|`.

It also proves what Baek's Prop 8.1.2 needs of `K_c`: a Minkowski combination of two such caps is a
cap (`IsCap.mix`), via the plane separation theorem
`p ∈ K ⟺ ∀ t, ⟪p, u_t⟫ ≤ h_K(t)` (`mem_of_forall_inner_le_supportFn`).

STATUS: [PROOF-C-local] round 1 (2026-09-22, Opus 5.5).
-/
import Sofa.CurveArea
import Sofa.EndPoint

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace Interval

namespace Sofa

variable {K : Set ℝ²}

/-! ## Separation in the plane -/

/-- **Separation**: a point below every supporting line of a compact convex set lies in it. -/
theorem mem_of_forall_inner_le_supportFn {S : Set ℝ²} (hS : IsCompact S) (hconv : Convex ℝ S)
    (hne : S.Nonempty) {p : ℝ²} (h : ∀ t, ⟪p, u t⟫ ≤ supportFn S t) : p ∈ S := by
  by_contra hp
  obtain ⟨f, c, hfS, hfp⟩ := geometric_hahn_banach_closed_point hconv hS.isClosed hp
  set w : ℝ² := (InnerProductSpace.toDual ℝ ℝ²).symm f with hwdef
  have hw : ∀ y, ⟪w, y⟫ = f y := fun y => InnerProductSpace.toDual_symm_apply
  have hw0 : w ≠ 0 := by
    intro h0
    obtain ⟨q, hq⟩ := hne
    have h1 := hfS q hq
    rw [← hw, h0, inner_zero_left] at h1
    rw [← hw, h0, inner_zero_left] at hfp
    linarith
  have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw0
  obtain ⟨ψ, hψ⟩ := exists_angle (z := ‖w‖⁻¹ • w) (norm_smul_inv_norm hw0)
  have key : ∀ y, ⟪y, u ψ⟫ = ‖w‖⁻¹ * f y := by
    intro y
    rw [hψ, real_inner_smul_right, real_inner_comm, hw]
  have h1 : supportFn S ψ ≤ ‖w‖⁻¹ * c := by
    refine (supportFn_le_iff hS hne ψ _).2 fun q hq => ?_
    rw [key]
    exact mul_le_mul_of_nonneg_left (hfS q hq).le (inv_nonneg.2 hnw.le)
  have h2 : ‖w‖⁻¹ * c < ⟪p, u ψ⟫ := by
    rw [key]
    exact mul_lt_mul_of_pos_left hfp (inv_pos.2 hnw)
  linarith [h ψ]

/-! ## Points and faces of a cap -/

section Cap

variable (hK : IsCap K (π / 2))
include hK

lemma IsCap.coord_one_nonneg {p : ℝ²} (hp : p ∈ K) : 0 ≤ p 1 := by
  have h := hK.inner_le hp (3 * π / 2)
  rw [hK.supportFn_three_pi_div_two, inner_eq, u_coord_zero, u_coord_one,
    show (3 : ℝ) * π / 2 = π / 2 + π by ring, cos_add_pi, sin_add_pi, cos_pi_div_two,
    sin_pi_div_two] at h
  linarith

lemma IsCap.neg_supportFn_pi_le {p : ℝ²} (hp : p ∈ K) : -supportFn K π ≤ p 0 := by
  have h := hK.inner_le hp π
  rw [inner_eq, u_coord_zero, u_coord_one, cos_pi, sin_pi] at h
  linarith

lemma IsCap.le_supportFn_zero {p : ℝ²} (hp : p ∈ K) : p 0 ≤ supportFn K 0 := by
  have h := hK.inner_le hp 0
  rw [inner_eq, u_coord_zero, u_coord_one, cos_zero, sin_zero] at h
  linarith

/-- Projecting a point of a cap straight down to the floor `y = 0` stays in the cap. -/
theorem IsCap.proj_floor_mem {q : ℝ²} (hq : q ∈ K) : q 0 • u 0 ∈ K := by
  have hq1 := hK.coord_one_nonneg hq
  rw [hK.mem_iff]
  intro r hr
  have hc : ⟪q 0 • u 0, u r⟫ = q 0 * cos r := by
    rw [real_inner_smul_left, inner_eq]; simp
  have hqr : ⟪q, u r⟫ = q 0 * cos r + q 1 * sin r := by rw [inner_eq, u_coord_zero, u_coord_one]
  rcases hr with (hr | hr) | hr
  · have hs := sin_nonneg_of_nonneg_of_le_pi (x := r) hr.1 (by linarith [hr.2, pi_pos])
    have := hK.inner_le hq r
    rw [hc]; nlinarith [mul_nonneg hq1 hs]
  · have hs := sin_nonneg_of_nonneg_of_le_pi (x := r) (by linarith [hr.1, pi_pos]) (by linarith [hr.2])
    have := hK.inner_le hq r
    rw [hc]; nlinarith [mul_nonneg hq1 hs]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    have h3 : r = 3 * π / 2 := by
      rcases hr with hr | hr
      · rw [hr]; ring
      · exact hr
    rw [hc, h3, hK.supportFn_three_pi_div_two,
      show (3 : ℝ) * π / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two]
    simp

/-- The floor corner `(h(0), 0)`. -/
theorem IsCap.cornerR_mem : supportFn K 0 • u 0 ∈ K := by
  have h := hK.proj_floor_mem (vtxP_mem hK.isCompact hK.nonempty 0)
  have e : vtxP K 0 0 = supportFn K 0 := by
    rw [vtxP]; simp
  rwa [e] at h

/-- The floor corner `(−h(π), 0)`. -/
theorem IsCap.cornerL_mem : supportFn K π • u π ∈ K := by
  have h := hK.proj_floor_mem (vtxP_mem hK.isCompact hK.nonempty π)
  have e : vtxP K π 0 • u 0 = supportFn K π • u π := by
    rw [vtxP]
    ext i; fin_cases i <;> simp [u, v]
  rwa [e] at h

/-- The left face of a cap reaches the floor: `e⁺_K(π) = 0`. -/
theorem IsCap.edgeMax_pi : edgeMax K π = 0 := by
  have hKc := hK.isCompact
  refine le_antisymm ?_ ?_
  · have h := hK.coord_one_nonneg (vtxP_mem hKc hK.nonempty π)
    have e : vtxP K π 1 = -edgeMax K π := by rw [vtxP]; simp [u, v]
    linarith
  · have hedge : supportFn K π • u π ∈ edge K π := by
      refine ⟨hK.cornerL_mem, ?_⟩
      simp only [supportLine, line, mem_ofPred_eq, real_inner_smul_left, inner_u_u, mul_one]
    have h := inner_v_le_edgeMax hKc hedge
    rwa [real_inner_smul_left, inner_u_v, mul_zero] at h

/-- `e⁻_K(π) = −|e_K(π)|` and `e⁺_K(0) = |e_K(0)|`. -/
theorem IsCap.edgeMin_pi : edgeMin K π = -edgeLength K π := by
  rw [edgeLength, hK.edgeMax_pi]; ring

theorem IsCap.edgeMax_zero : edgeMax K 0 = edgeLength K 0 := by
  rw [edgeLength, edgeMin_zero_of_isCap hK]; ring

/-- Between the left face and the floor, `h_K(t) = −h_K(π) cos t`. -/
theorem IsCap.supportFn_of_mem_Icc_pi {t : ℝ} (ht : t ∈ Icc π (3 * π / 2)) :
    supportFn K t = -supportFn K π * cos t := by
  have hc : cos t ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le (by linarith [ht.1, pi_pos])
    (by linarith [ht.2])
  have hs : sin t ≤ 0 := by
    have h := sin_nonpos_of_nonpos_of_neg_pi_le (x := t - 2 * π) (by linarith [ht.2, pi_pos])
      (by linarith [ht.1, pi_pos])
    rwa [sin_sub_two_pi] at h
  refine le_antisymm ?_ ?_
  · refine (supportFn_le_iff hK.isCompact hK.nonempty t _).2 fun p hp => ?_
    have h0 := hK.neg_supportFn_pi_le hp
    have h1 := hK.coord_one_nonneg hp
    rw [inner_eq, u_coord_zero, u_coord_one]
    nlinarith [mul_le_mul_of_nonpos_right h0 hc, mul_nonpos_of_nonneg_of_nonpos h1 hs]
  · have h := hK.inner_le hK.cornerL_mem t
    rwa [real_inner_smul_left, inner_u_u_eq_cos, cos_sub, cos_pi, sin_pi, zero_mul, add_zero,
      neg_one_mul, mul_neg, ← neg_mul] at h

/-- Between the floor and the right face, `h_K(t) = h_K(0) cos t`. -/
theorem IsCap.supportFn_of_mem_Icc_three_pi_div_two {t : ℝ} (ht : t ∈ Icc (3 * π / 2) (2 * π)) :
    supportFn K t = supportFn K 0 * cos t := by
  have hc : 0 ≤ cos t := by
    rw [← cos_sub_two_pi]
    exact cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2, pi_pos]⟩
  have hs : sin t ≤ 0 := by
    have h := sin_nonpos_of_nonpos_of_neg_pi_le (x := t - 2 * π) (by linarith [ht.2])
      (by linarith [ht.1, pi_pos])
    rwa [sin_sub_two_pi] at h
  refine le_antisymm ?_ ?_
  · refine (supportFn_le_iff hK.isCompact hK.nonempty t _).2 fun p hp => ?_
    have h0 := hK.le_supportFn_zero hp
    have h1 := hK.coord_one_nonneg hp
    rw [inner_eq, u_coord_zero, u_coord_one]
    nlinarith [mul_le_mul_of_nonneg_right h0 hc, mul_nonpos_of_nonneg_of_nonpos h1 hs]
  · have h := hK.inner_le hK.cornerR_mem t
    rwa [real_inner_smul_left, inner_u_u_eq_cos, zero_sub, cos_neg] at h

end Cap

/-! ## Lemma 8.3.5: `|K|` as a convex-curve functional -/

/-- `∫_a^b (cos² − sin²) = [sin · cos]_a^b`. -/
lemma integral_cos_sq_sub_sin_sq (a b : ℝ) :
    ∫ t in a..b, (cos t ^ 2 - sin t ^ 2) = sin b * cos b - sin a * cos a := by
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (fun t => sin t * cos t) (cos t ^ 2 - sin t ^ 2) t := by
    intro t _
    exact ((hasDerivAt_sin t).mul (hasDerivAt_cos t)).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((((continuous_cos.pow 2).sub (continuous_sin.pow 2))).intervalIntegrable a b)]

/-- On an open interval where `h_K = c · cos`, `(h_K² − (e⁺_K)²)` integrates to `c²·[sin cos]`. -/
lemma integral_sq_sub_sq_of_eq_cos (hK : IsCompact K) (hne : K.Nonempty) {a b c : ℝ} (hab : a ≤ b)
    (hcos : ∀ t ∈ Icc a b, supportFn K t = c * cos t) :
    ∫ t in a..b, (supportFn K t ^ 2 - edgeMax K t ^ 2)
      = c ^ 2 * (sin b * cos b - sin a * cos a) := by
  have hae : ∀ᵐ t ∂volume, t ∈ Ι a b →
      supportFn K t ^ 2 - edgeMax K t ^ 2 = c ^ 2 * (cos t ^ 2 - sin t ^ 2) := by
    have hb : ∀ᵐ t ∂volume, t ∉ ({b} : Set ℝ) := (Set.countable_singleton b).ae_notMem volume
    filter_upwards [ae_deriv_supportFn hK hne, hb] with t hdt htb ht
    rw [uIoc_of_le hab] at ht
    have ht' : t ∈ Ioo a b := ⟨ht.1, lt_of_le_of_ne ht.2 (by simpa using htb)⟩
    have hev : supportFn K =ᶠ[𝓝 t] fun s => c * cos s :=
      Filter.eventuallyEq_of_mem (Ioo_mem_nhds ht'.1 ht'.2)
        fun s hs => hcos s (Ioo_subset_Icc_self hs)
    have hder : HasDerivAt (supportFn K) (-(c * sin t)) t :=
      (((hasDerivAt_cos t).const_mul c).congr_of_eventuallyEq hev).congr_deriv (by ring)
    rw [← hdt, hder.deriv, hcos t (Ioo_subset_Icc_self ht')]
    ring
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul,
    integral_cos_sq_sub_sin_sq]

/-- **Baek Lemma 8.3.5, core**: for a cap with rotation angle `π/2` and nonempty interior,
`|K| = J(u^{0,π}_K) + ½h(π)|e_K(π)| + ½h(0)|e_K(0)|`. -/
theorem volumeReal_cap (hK : IsCap K (π / 2)) (hint : (interior K).Nonempty) :
    volume.real K = convJ K 0 π + supportFn K π * edgeLength K π / 2
      + supportFn K 0 * edgeLength K 0 / 2 := by
  have hKc := hK.isCompact
  have hne := hK.nonempty
  have hpi := pi_pos
  have hV := volumeReal_eq_integral_sq_sub_sq hKc hK.convex hint 0
  rw [zero_add] at hV
  have hi : ∀ x y : ℝ,
      IntervalIntegrable (fun t => supportFn K t ^ 2 - edgeMax K t ^ 2) volume x y :=
    fun x y => (((continuous_supportFn hKc hne).pow 2).intervalIntegrable x y).sub
      (intervalIntegrable_edgeMax_sq hKc hne x y)
  have hs1 := intervalIntegral.integral_add_adjacent_intervals (hi 0 π) (hi π (3 * π / 2))
  have hs2 := intervalIntegral.integral_add_adjacent_intervals (hi 0 (3 * π / 2))
    (hi (3 * π / 2) (2 * π))
  have hL := integral_sq_sub_sq_of_eq_cos hKc hne (a := π) (b := 3 * π / 2)
    (c := -supportFn K π) (by linarith) fun t ht => hK.supportFn_of_mem_Icc_pi ht
  have hR := integral_sq_sub_sq_of_eq_cos hKc hne (a := 3 * π / 2) (b := 2 * π)
    (c := supportFn K 0) (by linarith) fun t ht => hK.supportFn_of_mem_Icc_three_pi_div_two ht
  have e1 : sin (3 * π / 2) * cos (3 * π / 2) = 0 := by
    rw [show (3 : ℝ) * π / 2 = π / 2 + π by ring, cos_add_pi, cos_pi_div_two]; ring
  rw [e1, sin_pi, zero_mul, sub_zero, mul_zero] at hL
  rw [e1, sin_two_pi, zero_mul, sub_zero, mul_zero] at hR
  have hC := two_mul_convJ_eq hKc hne hpi
  rw [hK.edgeMin_pi, hK.edgeMax_zero] at hC
  linarith

/-! ## Minkowski combinations of caps (Baek Prop 8.1.2) -/

/-- **Caps with rotation angle `π/2` are closed under Minkowski combination.** -/
theorem isCap_mix {A B : Set ℝ²} (hA : IsCap A (π / 2)) (hB : IsCap B (π / 2)) {l : ℝ}
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) : IsCap (mix l A B) (π / 2) := by
  have hAc := hA.isCompact
  have hBc := hB.isCompact
  have hAne := hA.nonempty
  have hBne := hB.nonempty
  have hMc := isCompact_mix (l := l) hAc hBc
  have hMne := nonempty_mix (l := l) hAne hBne
  have hMconv := convex_mix (l := l) hA.convex hB.convex
  have hsf := fun t => supportFn_mix hAc hAne hBc hBne hl0 hl1 t
  refine ⟨hMconv, hMc, hMne, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsf, hA.supportFn_pi_div_two, hB.supportFn_pi_div_two]; ring
  · rw [hsf, hA.supportFn_pi_div_two, hB.supportFn_pi_div_two]; ring
  · rw [hsf, hA.supportFn_ω_add_pi, hB.supportFn_ω_add_pi]; ring
  · rw [hsf, hA.supportFn_three_pi_div_two, hB.supportFn_three_pi_div_two]; ring
  · ext p
    constructor
    · intro hp
      exact mem_iInter₂.2 fun t _ => le_supportFn hMc hp t
    · intro hp
      have hp' : ∀ t ∈ capAngles (π / 2), ⟪p, u t⟫ ≤ supportFn (mix l A B) t := by
        intro t ht; exact (mem_iInter₂.1 hp) t ht
      refine mem_of_forall_inner_le_supportFn hMc hMconv hMne fun t => ?_
      -- reduce `t` to `[0, 2π)`
      set s := toIcoMod two_pi_pos 0 t with hsdef
      have hs : s ∈ Ico 0 (0 + 2 * π) := toIcoMod_mem_Ico two_pi_pos 0 t
      obtain ⟨k, hk⟩ : ∃ k : ℤ, t = s + k * (2 * π) := by
        refine ⟨toIcoDiv two_pi_pos 0 t, ?_⟩
        rw [hsdef, toIcoMod]; simp
      have hut : u t = u s := by rw [hk, u_add_int_mul_two_pi]
      have hht : ∀ S : Set ℝ², supportFn S t = supportFn S s := fun S =>
        supportFn_congr_of_u_eq S hut
      rw [hut, hht]
      rw [zero_add] at hs
      have hpi := pi_pos
      -- the constraints at `π` and `3π/2`
      have hπ := hp' π (Or.inl (Or.inr ⟨by linarith [pi_pos], by linarith⟩))
      have h3 := hp' (3 * π / 2) (Or.inr (by simp))
      rw [inner_eq, u_coord_zero, u_coord_one, cos_pi, sin_pi] at hπ
      rw [hsf, hA.supportFn_three_pi_div_two, hB.supportFn_three_pi_div_two, inner_eq,
        u_coord_zero, u_coord_one, show (3 : ℝ) * π / 2 = π / 2 + π by ring, cos_add_pi,
        sin_add_pi, cos_pi_div_two, sin_pi_div_two] at h3
      have h0 := hp' 0 (Or.inl (Or.inl ⟨le_refl _, by linarith [pi_pos]⟩))
      rw [inner_eq, u_coord_zero, u_coord_one, cos_zero, sin_zero] at h0
      rcases le_or_gt s π with hsπ | hsπ
      · exact hp' s (by
          rcases le_or_gt s (π / 2) with h | h
          · exact Or.inl (Or.inl ⟨hs.1, h⟩)
          · exact Or.inl (Or.inr ⟨h.le, by linarith⟩))
      · rcases le_or_gt s (3 * π / 2) with hs3 | hs3
        · -- `[π, 3π/2]`
          have hMs : supportFn (mix l A B) s = -supportFn (mix l A B) π * cos s := by
            rw [hsf, hsf, hA.supportFn_of_mem_Icc_pi ⟨hsπ.le, hs3⟩,
              hB.supportFn_of_mem_Icc_pi ⟨hsπ.le, hs3⟩]; ring
          have hc : cos s ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith)
          have hsn : sin s ≤ 0 := by
            have h := sin_nonpos_of_nonpos_of_neg_pi_le (x := s - 2 * π) (by linarith)
              (by linarith)
            rwa [sin_sub_two_pi] at h
          rw [hMs, inner_eq, u_coord_zero, u_coord_one]
          have hp0 : -supportFn (mix l A B) π ≤ p 0 := by linarith
          nlinarith [mul_le_mul_of_nonpos_right hp0 hc, mul_nonpos_of_nonneg_of_nonpos
            (show 0 ≤ p 1 by linarith) hsn]
        · -- `[3π/2, 2π)`
          have hMs : supportFn (mix l A B) s = supportFn (mix l A B) 0 * cos s := by
            rw [hsf, hsf, hA.supportFn_of_mem_Icc_three_pi_div_two ⟨hs3.le, hs.2.le⟩,
              hB.supportFn_of_mem_Icc_three_pi_div_two ⟨hs3.le, hs.2.le⟩]; ring
          have hc : 0 ≤ cos s := by
            rw [← cos_sub_two_pi]
            exact cos_nonneg_of_mem_Icc ⟨by linarith, by linarith [hs.2]⟩
          have hsn : sin s ≤ 0 := by
            have h := sin_nonpos_of_nonpos_of_neg_pi_le (x := s - 2 * π) (by linarith [hs.2])
              (by linarith)
            rwa [sin_sub_two_pi] at h
          rw [hMs, inner_eq, u_coord_zero, u_coord_one]
          nlinarith [mul_le_mul_of_nonneg_right h0 hc, mul_nonpos_of_nonneg_of_nonpos
            (show 0 ≤ p 1 by linarith) hsn]

/-- A Minkowski combination of a body with nonempty interior and a nonempty body has nonempty
interior (for `λ < 1`; for `λ = 1` it is the second body). -/
theorem interior_mix_nonempty {A B : Set ℝ²} (hA : (interior A).Nonempty) (hB : (interior B).Nonempty)
    {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) : (interior (mix l A B)).Nonempty := by
  rcases lt_or_eq_of_le hl1 with hl | hl
  · obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    have hb' : b ∈ B := interior_subset hb
    have hne : (1 - l) ≠ 0 := by linarith
    -- the homeomorphism `x ↦ (1-l) x + l b`
    set f : ℝ² ≃ₜ ℝ² := (Homeomorph.smulOfNeZero (1 - l) hne).trans (Homeomorph.addRight (l • b))
    have hsub : f '' A ⊆ mix l A B := by
      rintro _ ⟨x, hx, rfl⟩
      exact mem_mix.2 ⟨x, hx, b, hb', rfl⟩
    have hint : f '' interior A ⊆ interior (mix l A B) := by
      rw [f.image_interior]
      exact interior_mono hsub
    exact ⟨f a, hint ⟨a, ha, rfl⟩⟩
  · subst hl
    obtain ⟨a, ha⟩ := hA
    have ha' : a ∈ A := interior_subset ha
    have heq : mix 1 A B = B := by
      ext q
      constructor
      · intro hq
        obtain ⟨x, _, y, hy, hxy⟩ := mem_mix.1 hq
        rw [← hxy, sub_self, zero_smul, zero_add, one_smul]; exact hy
      · intro hq
        exact mem_mix.2 ⟨a, ha', q, hq, by rw [sub_self, zero_smul, zero_add, one_smul]⟩
    rw [heq]; exact hB

end Sofa
