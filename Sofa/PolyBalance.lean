/-
# Sofa/PolyBalance.lean — balancedness of maximum polygon caps (Baek Thm 3.4.9, 3.4.10)

Basic properties of `capH` (convex, compact, monotone, translation equivariant), the criterion
for `capH h` to be a polygon cap, Prop 3.3.7, Lemma 3.4.8 and the two main theorems of §3.4.

STATUS: in progress (2026-09-17, Opus 5).
-/
import Sofa.PolyGraph

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {ω : ℝ} {Θ : Finset ℝ}

section CapH

variable (hP : PolySetup ω Θ)
include hP

lemma capH_eq_iInter (h : ℝ → ℝ) :
    capH ω Θ h = (⋂ s ∈ diamondFin ω Θ, hpLe s (h s)) ∩ ⋂ s ∈ fanFin ω, hpGe s (h s - 1) := by
  ext p
  rw [mem_capH_iff hP]
  simp only [mem_inter_iff, mem_iInter₂, hpLe, hpGe, mem_ofPred_eq]
  exact ⟨fun hp => ⟨hp.2, hp.1⟩, fun hp => ⟨hp.2, hp.1⟩⟩

lemma convex_capH (h : ℝ → ℝ) : Convex ℝ (capH ω Θ h) := by
  rw [capH_eq_iInter hP]
  exact (convex_iInter₂ fun s _ => convex_halfSpace_le (isLinearMap_inner_u s) _).inter
    (convex_iInter₂ fun s _ => convex_halfSpace_ge (isLinearMap_inner_u s) _)

lemma isClosed_capH (h : ℝ → ℝ) : IsClosed (capH ω Θ h) := by
  rw [capH_eq_iInter hP]
  exact (isClosed_biInter fun s _ => isClosed_hpLe s (h s)).inter
    (isClosed_biInter fun s _ => isClosed_hpGe s (h s - 1))

lemma isBounded_capH (h : ℝ → ℝ) : Bornology.IsBounded (capH ω Θ h) := by
  obtain ⟨t, ht⟩ := hP.nonempty
  have hs := hP.sin_pos_Θ ht
  have hc := hP.cos_pos_Θ ht
  set b := |h (π / 2)| + 1 with hb
  have hb0 : 0 ≤ b := by positivity
  refine Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ℝ²))
    (r := ((|h t| + b) / cos t + (|h (t + π / 2)| + b) / sin t) + b)) ?_
  intro p hp
  rw [mem_closedBall_zero_iff]
  obtain ⟨hlow, hup⟩ := (mem_capH_iff hP).1 hp
  have h1 : ⟪p, u t⟫ ≤ h t := hup t (mem_diamondFin_of_mem ht)
  have h2 : ⟪p, u (t + π / 2)⟫ ≤ h (t + π / 2) := hup _ (add_mem_diamondFin ht)
  have h3 : ⟪p, u (π / 2)⟫ ≤ h (π / 2) := hup _ (mem_diamondFin_of_fan (pi_div_two_mem_fanFin ω))
  have h4 : h (π / 2) - 1 ≤ ⟪p, u (π / 2)⟫ := hlow _ (pi_div_two_mem_fanFin ω)
  rw [inner_u_pi_div_two] at h3 h4
  rw [inner_u_decomp] at h1
  rw [inner_u_decomp, cos_add_pi_div_two, sin_add_pi_div_two] at h2
  have hy : |p 1| ≤ b := by
    rw [abs_le, hb]
    constructor <;> [skip; skip] <;>
      [linarith [le_abs_self (h (π / 2)), neg_abs_le (h (π / 2))];
       linarith [le_abs_self (h (π / 2))]]
  have hy' := abs_le.1 hy
  have hx : |p 0| ≤ (|h t| + b) / cos t + (|h (t + π / 2)| + b) / sin t := by
    have hA' : -p 1 ≤ b := by linarith [hy'.1]
    have e1 : p 0 ≤ (|h t| + b) / cos t := by
      rw [le_div_iff₀ hc]
      have hA := mul_le_mul_of_nonneg_right hA' hs.le
      have hB := mul_le_mul_of_nonneg_left (sin_le_one t) hb0
      have := le_abs_self (h t)
      nlinarith
    have e2 : -((|h (t + π / 2)| + b) / sin t) ≤ p 0 := by
      rw [neg_le, le_div_iff₀ hs]
      have hA := mul_le_mul_of_nonneg_right hA' hc.le
      have hB := mul_le_mul_of_nonneg_left (cos_le_one t) hb0
      have := le_abs_self (h (t + π / 2))
      nlinarith
    have hA : 0 ≤ (|h t| + b) / cos t := by positivity
    have hB : 0 ≤ (|h (t + π / 2)| + b) / sin t := by positivity
    rw [abs_le]
    constructor <;> linarith
  exact norm_le_add_of_abs_coord_le hx hy

lemma isCompact_capH (h : ℝ → ℝ) : IsCompact (capH ω Θ h) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_capH hP h) (isBounded_capH hP h)

lemma capH_mono {h h' : ℝ → ℝ} (hle : ∀ s ∈ diamondFin ω Θ, h s ≤ h' s)
    (heq : ∀ s ∈ fanFin ω, h' s = h s) : capH ω Θ h ⊆ capH ω Θ h' := by
  intro p hp
  obtain ⟨hlow, hup⟩ := (mem_capH_iff hP).1 hp
  refine (mem_capH_iff hP).2 ⟨fun s hs => ?_, fun s hs => (hup s hs).trans (hle s hs)⟩
  rw [heq s hs]
  exact hlow s hs

lemma nicheH_mono {h h' : ℝ → ℝ} (hle : ∀ s ∈ diamondFin ω Θ, h s ≤ h' s)
    (heq : ∀ s ∈ fanFin ω, h' s = h s) :
    nicheH ω Θ hP.nonempty h ⊆ nicheH ω Θ hP.nonempty h' := by
  intro p hp
  obtain ⟨hlow, t, ht, h1, h2⟩ := (mem_nicheH_iff hP).1 hp
  refine (mem_nicheH_iff hP).2 ⟨fun s hs => ?_, t, ht, ?_, ?_⟩
  · rw [heq s hs]; exact hlow s hs
  · exact h1.trans_le (by linarith [hle t (mem_diamondFin_of_mem ht)])
  · exact h2.trans_le (by linarith [hle _ (add_mem_diamondFin ht)])

lemma supportFn_capH_le (h : ℝ → ℝ) {s : ℝ} (hs : s ∈ diamondFin ω Θ)
    (hne : (capH ω Θ h).Nonempty) : supportFn (capH ω Θ h) s ≤ h s := by
  rw [supportFn_le_iff (isCompact_capH hP h) hne]
  exact fun p hp => ((mem_capH_iff hP).1 hp).2 s hs

/-- If `capH h` touches all four lines `l(ω, h ω)`, `l(π/2, h (π/2))`, `l(ω, h ω - 1)`,
`l(π/2, h (π/2) - 1)` and `h ω = h (π/2) = 1`, then it is a polygon cap. -/
theorem isPolyCap_capH {h : ℝ → ℝ} (h1 : h ω = 1) (h2 : h (π / 2) = 1)
    (htop : ∀ s ∈ fanFin ω, ∃ p ∈ capH ω Θ h, ⟪p, u s⟫ = h s)
    (hbot : ∀ s ∈ fanFin ω, ∃ p ∈ capH ω Θ h, ⟪p, u s⟫ = h s - 1) :
    IsPolyCap ω Θ (capH ω Θ h) := by
  obtain ⟨p₀, hp₀, -⟩ := htop ω (self_mem_fanFin ω)
  have hne : (capH ω Θ h).Nonempty := ⟨p₀, hp₀⟩
  have hcomp := isCompact_capH hP h
  have hsup : ∀ s ∈ fanFin ω, supportFn (capH ω Θ h) s = h s := by
    intro s hs
    refine le_antisymm (supportFn_capH_le hP h (mem_diamondFin_of_fan hs) hne) ?_
    obtain ⟨p, hp, hps⟩ := htop s hs
    exact hps ▸ le_supportFn hcomp hp s
  have hsupb : ∀ s ∈ fanFin ω, supportFn (capH ω Θ h) (s + π) = -(h s - 1) := by
    intro s hs
    refine le_antisymm ?_ ?_
    · rw [supportFn_le_iff hcomp hne]
      intro p hp
      rw [u_add_pi, inner_neg_right, neg_le_neg_iff]
      exact ((mem_capH_iff hP).1 hp).1 s hs
    · obtain ⟨p, hp, hps⟩ := hbot s hs
      have := le_supportFn hcomp hp (s + π)
      rwa [u_add_pi, inner_neg_right, hps] at this
  have hω' : supportFn (capH ω Θ h) (ω + π) = 0 := by
    rw [hsupb ω (self_mem_fanFin ω), h1]; ring
  have hπ' : supportFn (capH ω Θ h) (3 * π / 2) = 0 := by
    have e : 3 * π / 2 = π / 2 + π := by ring
    rw [e, hsupb _ (pi_div_two_mem_fanFin ω), h2]; ring
  have hsubD : ∀ s ∈ diamondFin ω Θ, s ∈ capAngles ω := by
    intro s hs
    rcases mem_diamondFin.1 hs with hs' | ⟨t, ht, rfl⟩ | hs'
    · exact Or.inl (mem_Jω_of_mem_Icc ⟨(hP.mem_Θ hs').1.le, (hP.mem_Θ hs').2.le⟩)
    · exact Or.inl (add_pi_div_two_mem_Jω ⟨(hP.mem_Θ ht).1.le, (hP.mem_Θ ht).2.le⟩)
    · rcases mem_fanFin.1 hs' with rfl | rfl
      · exact Or.inl (mem_Jω_of_mem_Icc ⟨hP.pos.le, le_rfl⟩)
      · exact Or.inl (Or.inr ⟨le_rfl, by linarith [hP.pos]⟩)
  have hkey : ∀ (S : Set ℝ), (∀ s ∈ diamondFin ω Θ, s ∈ S) → ω + π ∈ S → 3 * π / 2 ∈ S →
      (⋂ s ∈ S, hpLe s (supportFn (capH ω Θ h) s)) ⊆ capH ω Θ h := by
    intro S hSD hSω hSπ p hp
    rw [mem_iInter₂] at hp
    refine (mem_capH_iff hP).2 ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rcases mem_fanFin.1 hs with rfl | rfl
      · have := hp _ hSω
        rw [hpLe, mem_ofPred_eq, hω', u_add_pi, inner_neg_right] at this
        rw [h1]; linarith
      · have := hp _ hSπ
        rw [hpLe, mem_ofPred_eq, hπ', show 3 * π / 2 = π / 2 + π by ring, u_add_pi,
          inner_neg_right] at this
        rw [h2]; linarith
    · have := hp s (hSD s hs)
      rw [hpLe, mem_ofPred_eq] at this
      exact this.trans (supportFn_capH_le hP h hs hne)
  refine ⟨⟨convex_capH hP h, hcomp, hne, by rw [hsup ω (self_mem_fanFin ω), h1],
    by rw [hsup _ (pi_div_two_mem_fanFin ω), h2], hω', hπ', ?_⟩, ?_⟩
  · refine subset_antisymm (fun p hp => mem_iInter₂.2 fun s _ => le_supportFn hcomp hp s)
      (hkey (capAngles ω) hsubD (Or.inr (by simp)) (Or.inr (by simp)))
  · refine subset_antisymm (fun p hp => mem_iInter₂.2 fun s _ => le_supportFn hcomp hp s)
      (hkey (polyCapAngles ω Θ) (fun s hs => Or.inl (coe_diamondFin ▸ hs))
        (Or.inr (by simp)) (Or.inr (by simp)))

end CapH

/-! ## The graphs of a polygon cap -/

section CapGraph

variable (hP : PolySetup ω Θ) {K : Set ℝ²}

include hP in
lemma capH_eq_iInter_polyCapAngles (hX : IsCap K ω) :
    capH ω Θ (supportFn K) = ⋂ s ∈ polyCapAngles ω Θ, hpLe s (supportFn K s) := by
  have e1 : ∀ p : ℝ², p ∈ hpLe (ω + π) (supportFn K (ω + π)) ↔
      supportFn K ω - 1 ≤ ⟪p, u ω⟫ := by
    intro p
    rw [hpLe, mem_ofPred_eq, hX.supportFn_ω_add_pi, u_add_pi, inner_neg_right, hX.supportFn_ω]
    constructor <;> intro h <;> linarith
  have e2 : ∀ p : ℝ², p ∈ hpLe (3 * π / 2) (supportFn K (3 * π / 2)) ↔
      supportFn K (π / 2) - 1 ≤ ⟪p, u (π / 2)⟫ := by
    intro p
    rw [hpLe, mem_ofPred_eq, hX.supportFn_three_pi_div_two, u_three_pi_div_two, inner_neg_right,
      hX.supportFn_pi_div_two]
    constructor <;> intro h <;> linarith
  ext p
  rw [mem_capH_iff hP]
  simp only [polyCapAngles, mem_iInter₂, mem_union, mem_insert_iff, mem_singleton_iff,
    ← coe_diamondFin, Finset.mem_coe]
  constructor
  · rintro ⟨hlow, hup⟩ s hs
    rcases hs with hs | hs | hs
    · exact hup s hs
    · subst hs; exact (e1 p).2 (hlow ω (self_mem_fanFin ω))
    · subst hs; exact (e2 p).2 (hlow _ (pi_div_two_mem_fanFin ω))
  · intro hp
    refine ⟨fun s hs => ?_, fun s hs => hp s (Or.inl hs)⟩
    rcases mem_fanFin.1 hs with hs' | hs'
    · rw [hs']; exact (e1 p).1 (hp _ (Or.inr (Or.inl rfl)))
    · rw [hs']; exact (e2 p).1 (hp _ (Or.inr (Or.inr rfl)))

include hP in
lemma capH_supportFn (hK : IsPolyCap ω Θ K) : capH ω Θ (supportFn K) = K :=
  (capH_eq_iInter_polyCapAngles hP hK.1).trans hK.2.symm

variable (hK : IsPolyCap ω Θ K)
include hP hK

lemma posU_subset_Iio : posU ω Θ (supportFn K) ⊆ Iio (supportFn K 0) := by
  have hmem : ∀ x ∈ posU ω Θ (supportFn K), x ≤ supportFn K 0 := by
    intro x hx
    have hx' : floorF ω (supportFn K) x < roofU ω Θ (supportFn K) x := hx
    set y := (floorF ω (supportFn K) x + roofU ω Θ (supportFn K) x) / 2 with hy
    have hp : pt x y ∈ capH ω Θ (supportFn K) := by
      constructor <;> simp only [pt_zero, pt_one, hy] <;> linarith
    rw [capH_supportFn hP hK] at hp
    have := hK.1.inner_le hp 0
    rwa [inner_u_zero, pt_zero] at this
  intro x hx
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isOpen_posU (ω := ω) (Θ := Θ) (supportFn K)) x hx
  have : x + δ / 2 ∈ posU ω Θ (supportFn K) := by
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq]
    rw [show x + δ / 2 - x = δ / 2 by ring, abs_of_pos (by linarith)]
    linarith
  have := hmem _ this
  exact lt_of_lt_of_le (by linarith) this

/-- The niche lives strictly between the two corners (Thm 2.5.5). -/
lemma posR_subset_Ioo :
    posR ω Θ hP.nonempty (supportFn K) ⊆
      Ioo (-(supportFn K (ω + π / 2) * sin ω)) (supportFn K 0) := by
  intro x hx
  have hx' : floorF ω (supportFn K) x < roofR Θ hP.nonempty (supportFn K) x := hx
  rw [roofR, Finset.lt_sup'_iff] at hx'
  obtain ⟨t, ht, hmin⟩ := hx'
  rw [lt_min_iff] at hmin
  obtain ⟨ht0, ht1⟩ := hP.mem_Θ ht
  have hst := hP.sin_pos_Θ ht
  have hct := hP.cos_pos_Θ ht
  have hωle : ω ≤ π / 2 := hP.le
  have hω0 : 0 < ω := hP.pos
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  have hcωt : 0 < cos (ω - t) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hf1 : lineFn (π / 2) (supportFn K (π / 2) - 1) x ≤ floorF ω (supportFn K) x :=
    Finset.le_sup' (fun s => lineFn s (supportFn K s - 1) x) (pi_div_two_mem_fanFin ω)
  have hf2 : lineFn ω (supportFn K ω - 1) x ≤ floorF ω (supportFn K) x :=
    Finset.le_sup' (fun s => lineFn s (supportFn K s - 1) x) (self_mem_fanFin ω)
  rw [hK.1.supportFn_pi_div_two, sub_self, lineFn, cos_pi_div_two, sin_pi_div_two] at hf1
  simp only [mul_zero, sub_zero, zero_div] at hf1
  rw [hK.1.supportFn_ω, sub_self] at hf2
  constructor
  · -- left gap
    have hZ := hK.1.gapZ_pos hP.le ⟨ht0, ht1⟩
    rw [gapZ, sub_pos, div_lt_iff₀ hcωt] at hZ
    have hy : lineFn ω 0 x = -x * cos ω / sin ω := by rw [lineFn]; ring
    have hd : -x * cos ω / sin ω <
        (supportFn K (t + π / 2) - 1 + x * sin t) / cos t := by
      have e : lineFn (t + π / 2) (supportFn K (t + π / 2) - 1) x
          = (supportFn K (t + π / 2) - 1 + x * sin t) / cos t := by
        rw [lineFn, cos_add_pi_div_two, sin_add_pi_div_two]; ring
      rw [← e, ← hy]
      exact lt_of_le_of_lt hf2 hmin.2
    rw [div_lt_div_iff₀ hsω hct] at hd
    have key : -x * cos (ω - t) < (supportFn K (t + π / 2) - 1) * sin ω := by
      rw [cos_sub]; nlinarith [hd]
    have hZ' : (supportFn K (t + π / 2) - 1) * sin ω <
        supportFn K (ω + π / 2) * cos (ω - t) * sin ω := mul_lt_mul_of_pos_right hZ hsω
    have hprod : (-x - supportFn K (ω + π / 2) * sin ω) * cos (ω - t) < 0 := by
      nlinarith [key, hZ']
    nlinarith [hprod, hcωt]
  · -- right gap
    have hW := hK.1.gapW_pos hP.le ⟨ht0, ht1⟩
    rw [gapW, sub_pos, div_lt_iff₀ hct] at hW
    have hb : 0 < lineFn t (supportFn K t - 1) x := lt_of_le_of_lt hf1 hmin.1
    rw [lineFn, lt_div_iff₀ hst] at hb
    nlinarith [hb, hW]

/-- A point of the cap of positive height and positive `u_ω`-coordinate witnesses `x ∈ I`. -/
lemma mem_posU_of_mem {p : ℝ²} (hp : p ∈ K) (hy : 0 < p 1) (hu : 0 < ⟪p, u ω⟫) :
    p 0 ∈ posU ω Θ (supportFn K) := by
  have hlow : floorF ω (supportFn K) (p 0) < p 1 := by
    rw [floorF_lt_iff hP, forall_fanFin, hK.1.supportFn_ω, hK.1.supportFn_pi_div_two]
    refine ⟨by linarith, ?_⟩
    rw [inner_u_pi_div_two]
    linarith
  have hup : p 1 ≤ roofU ω Θ (supportFn K) (p 0) := by
    rw [← capH_supportFn hP hK] at hp
    exact hp.2
  exact lt_of_lt_of_le hlow hup

/-- Between the two corners the cap has positive height: `(x_C, h(0)) ⊆ I`. -/
lemma Ioo_subset_posU :
    Ioo (-(supportFn K (ω + π / 2) * sin ω)) (supportFn K 0) ⊆ posU ω Θ (supportFn K) := by
  have hA : hK.1.cornerA ∈ K := hK.1.cornerA_mem hP.pos hP.le
  have hC : hK.1.cornerC ∈ K := hK.1.cornerC_mem hP.pos hP.le
  have hAx : hK.1.cornerA 0 = supportFn K 0 := by rw [hK.1.cornerA_eq, pt_zero]
  have hAy : hK.1.cornerA 1 = 0 := by rw [hK.1.cornerA_eq, pt_one]
  have hAu : 0 ≤ ⟪hK.1.cornerA, u ω⟫ := (hK.1.subset_fan hA).2
  have hCx : hK.1.cornerC 0 = -(supportFn K (ω + π / 2) * sin ω) := by
    rw [IsCap.cornerC, PiLp.smul_apply, v_coord_zero, smul_eq_mul]; ring
  have hCy : 0 ≤ hK.1.cornerC 1 := (hK.1.subset_fan hC).1
  have hCu : ⟪hK.1.cornerC, u ω⟫ = 0 := by
    rw [IsCap.cornerC, real_inner_smul_left, inner_v_u, mul_zero]
  obtain ⟨pT, hpT, hpT1⟩ := exists_supportFn_eq hK.1.isCompact hK.1.nonempty (π / 2)
  obtain ⟨pR, hpR, hpR1⟩ := exists_supportFn_eq hK.1.isCompact hK.1.nonempty ω
  rw [hK.1.supportFn_pi_div_two, inner_u_pi_div_two] at hpT1
  rw [hK.1.supportFn_ω] at hpR1
  set m : ℝ² := (2⁻¹ : ℝ) • pT + (2⁻¹ : ℝ) • pR with hm_def
  have hm : m ∈ K := hK.1.convex hpT hpR (by norm_num) (by norm_num) (by norm_num)
  have hmy : 0 < m 1 := by
    have : (0 : ℝ) ≤ pR 1 := (hK.1.subset_fan hpR).1
    rw [hm_def, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, hpT1]
    linarith
  have hmu : 0 < ⟪m, u ω⟫ := by
    have : (0 : ℝ) ≤ ⟪pT, u ω⟫ := (hK.1.subset_fan hpT).2
    rw [hm_def, inner_add_left, real_inner_smul_left, real_inner_smul_left, hpR1]
    linarith
  have hmA : m 0 ≤ supportFn K 0 := by
    have := hK.1.inner_le hm 0
    rwa [inner_u_zero] at this
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  rcases le_or_gt (m 0) x with hcase | hcase
  · -- between `m` and the right corner
    have hden : 0 < supportFn K 0 - m 0 := by linarith
    set l := (supportFn K 0 - x) / (supportFn K 0 - m 0) with hl
    have hl0 : 0 < l := div_pos (by linarith) hden
    have hl1 : l ≤ 1 := (div_le_one hden).2 (by linarith)
    have hp : l • m + (1 - l) • hK.1.cornerA ∈ K :=
      hK.1.convex hm hA hl0.le (by linarith) (by ring)
    have hpx : (l • m + (1 - l) • hK.1.cornerA) 0 = x := by
      have hkey : l * (m 0 - supportFn K 0) = x - supportFn K 0 := by
        rw [hl, div_mul_eq_mul_div, div_eq_iff (ne_of_gt hden)]
        ring
      rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, hAx]
      linear_combination hkey
    have hpy : 0 < (l • m + (1 - l) • hK.1.cornerA) 1 := by
      rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, hAy]
      have := mul_pos hl0 hmy
      nlinarith
    have hpu : 0 < ⟪l • m + (1 - l) • hK.1.cornerA, u ω⟫ := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      have h1 := mul_pos hl0 hmu
      have h2 : 0 ≤ (1 - l) * ⟪hK.1.cornerA, u ω⟫ := mul_nonneg (by linarith) hAu
      linarith
    have := mem_posU_of_mem hP hK hp hpy hpu
    rwa [hpx] at this
  · -- between the left corner and `m`
    have hden : 0 < m 0 - -(supportFn K (ω + π / 2) * sin ω) := by linarith
    set l := (x - -(supportFn K (ω + π / 2) * sin ω)) /
      (m 0 - -(supportFn K (ω + π / 2) * sin ω)) with hl
    have hl0 : 0 < l := div_pos (by linarith) hden
    have hl1 : l ≤ 1 := (div_le_one hden).2 (by linarith)
    have hp : l • m + (1 - l) • hK.1.cornerC ∈ K :=
      hK.1.convex hm hC hl0.le (by linarith) (by ring)
    have hpx : (l • m + (1 - l) • hK.1.cornerC) 0 = x := by
      have hkey : l * (m 0 - -(supportFn K (ω + π / 2) * sin ω)) =
          x - -(supportFn K (ω + π / 2) * sin ω) := by
        rw [hl, div_mul_eq_mul_div, div_eq_iff (ne_of_gt hden)]
      rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, hCx]
      linear_combination hkey
    have hpy : 0 < (l • m + (1 - l) • hK.1.cornerC) 1 := by
      rw [PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul]
      have h1 := mul_pos hl0 hmy
      have h2 : 0 ≤ (1 - l) * hK.1.cornerC 1 := mul_nonneg (by linarith) hCy
      linarith
    have hpu : 0 < ⟪l • m + (1 - l) • hK.1.cornerC, u ω⟫ := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hCu]
      have h1 := mul_pos hl0 hmu
      linarith
    have := mem_posU_of_mem hP hK hp hpy hpu
    rwa [hpx] at this

/-- `J ⊆ I`: the niche lies over the cap. -/
lemma posR_subset_posU :
    posR ω Θ hP.nonempty (supportFn K) ⊆ posU ω Θ (supportFn K) :=
  (posR_subset_Ioo hP hK).trans (Ioo_subset_posU hP hK)

end CapGraph

/-! ## Finiteness, translation, and Prop 3.3.7 -/

section Translate

variable (hP : PolySetup ω Θ)
include hP

lemma volume_capH_ne_top (h : ℝ → ℝ) : volume (capH ω Θ h) ≠ ⊤ := by
  have e : ∫⁻ x, ENNReal.ofReal (roofU ω Θ h x - floorF ω h x) =
      ENNReal.ofReal (∫ x, max (roofU ω Θ h x - floorF ω h x) 0) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_posPart_U hP h)
      (Eventually.of_forall fun x => le_max_right _ _)]
    exact lintegral_congr fun x => ofReal_eq_ofReal_max_zero _
  rw [capH, volume_between_Icc (continuous_floorF h).measurable (continuous_roofU h).measurable, e]
  exact ENNReal.ofReal_ne_top

lemma volume_nicheH_ne_top (h : ℝ → ℝ) : volume (nicheH ω Θ hP.nonempty h) ≠ ⊤ := by
  have e : ∫⁻ x, ENNReal.ofReal (roofR Θ hP.nonempty h x - floorF ω h x) =
      ENNReal.ofReal (∫ x, max (roofR Θ hP.nonempty h x - floorF ω h x) 0) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_posPart_R hP h)
      (Eventually.of_forall fun x => le_max_right _ _)]
    exact lintegral_congr fun x => ofReal_eq_ofReal_max_zero _
  rw [nicheH, volume_between_Ico (continuous_floorF h).measurable
    (continuous_roofR hP.nonempty h).measurable, e]
  exact ENNReal.ofReal_ne_top

variable (ω Θ) in
/-- Translating a support function: `h_{K+w}(s) = h_K(s) + ⟪w, u_s⟫`. -/
def transH (h : ℝ → ℝ) (w : ℝ²) : ℝ → ℝ := fun s => h s + ⟪w, u s⟫

lemma capH_transH (h : ℝ → ℝ) (w : ℝ²) :
    capH ω Θ (transH h w) = (fun p => p - w) ⁻¹' capH ω Θ h := by
  ext p
  rw [mem_preimage, mem_capH_iff hP, mem_capH_iff hP]
  simp only [transH, inner_sub_left]
  constructor
  · rintro ⟨hlow, hup⟩
    exact ⟨fun s hs => by linarith [hlow s hs], fun s hs => by linarith [hup s hs]⟩
  · rintro ⟨hlow, hup⟩
    exact ⟨fun s hs => by linarith [hlow s hs], fun s hs => by linarith [hup s hs]⟩

lemma nicheH_transH (h : ℝ → ℝ) (w : ℝ²) :
    nicheH ω Θ hP.nonempty (transH h w) = (fun p => p - w) ⁻¹' nicheH ω Θ hP.nonempty h := by
  ext p
  rw [mem_preimage, mem_nicheH_iff hP, mem_nicheH_iff hP]
  simp only [transH, inner_sub_left]
  constructor
  · rintro ⟨hlow, t, ht, h1, h2⟩
    exact ⟨fun s hs => by linarith [hlow s hs], t, ht, by linarith, by linarith⟩
  · rintro ⟨hlow, t, ht, h1, h2⟩
    exact ⟨fun s hs => by linarith [hlow s hs], t, ht, by linarith, by linarith⟩

omit hP in
lemma measureReal_preimage_sub (A : Set ℝ²) (w : ℝ²) :
    volume.real ((fun p => p - w) ⁻¹' A) = volume.real A := by
  simp only [measureReal_def, sub_eq_add_neg, measure_preimage_add_right]

theorem areaH_transH (h : ℝ → ℝ) (w : ℝ²) :
    areaH ω Θ hP.nonempty (transH h w) = areaH ω Θ hP.nonempty h := by
  rw [areaH_eq hP, areaH_eq hP, capH_transH hP, nicheH_transH hP, measureReal_preimage_sub,
    measureReal_preimage_sub]

/-- **Prop 3.3.7.** -/
theorem areaH_le_areaH_supportFn {h : ℝ → ℝ} (h1 : h ω = 1) (h2 : h (π / 2) = 1)
    (hX : IsPolyCap ω Θ (capH ω Θ h)) :
    areaH ω Θ hP.nonempty h ≤ areaH ω Θ hP.nonempty (supportFn (capH ω Θ h)) := by
  set k := supportFn (capH ω Θ h) with hk
  have hk_le : ∀ s ∈ diamondFin ω Θ, k s ≤ h s := fun s hs =>
    supportFn_capH_le hP h hs hX.1.nonempty
  have hk_fan : ∀ s ∈ fanFin ω, h s = k s := by
    intro s hs
    rcases mem_fanFin.1 hs with hs' | hs' <;> rw [hs', hk]
    · rw [h1, hX.1.supportFn_ω]
    · rw [h2, hX.1.supportFn_pi_div_two]
  have hcap : capH ω Θ k = capH ω Θ h := capH_supportFn hP hX
  have hniche : nicheH ω Θ hP.nonempty k ⊆ nicheH ω Θ hP.nonempty h :=
    nicheH_mono hP hk_le fun s hs => hk_fan s hs
  rw [areaH_eq hP, areaH_eq hP, hcap]
  have := measureReal_mono hniche (volume_nicheH_ne_top hP h)
  linarith

end Translate

/-! ## Lemma 3.4.8: pushing one line keeps a cap translate -/

section Push

variable (hP : PolySetup ω Θ) {K : Set ℝ²}
include hP

omit hP in
lemma erase_nonempty (hP : PolySetup ω Θ) (t : ℝ) : ((diamondFin ω Θ).erase t).Nonempty := by
  obtain ⟨t₁, ht₁⟩ := hP.nonempty
  by_cases h : t₁ = t
  · refine ⟨t₁ + π / 2, Finset.mem_erase.2 ⟨?_, add_mem_diamondFin ht₁⟩⟩
    rw [← h]
    exact hP.add_ne ht₁ ht₁
  · exact ⟨t₁, Finset.mem_erase.2 ⟨h, mem_diamondFin_of_mem ht₁⟩⟩

/-- With `σ(t) > 0` the pushed line still touches the pushed cap. -/
theorem exists_top_point_push (_hK : IsPolyCap ω Θ K) {t : ℝ} (ht : t ∈ diamondFin ω Θ)
    (hσ : 0 < sigmaH ω Θ (supportFn K) t) :
    ∃ δ > 0, ∀ ε ∈ Ioc 0 δ, ∃ p ∈ capH ω Θ (pushH (supportFn K) t ε),
      ⟪p, u t⟫ = supportFn K t + ε := by
  set h := supportFn K with hh
  have hsin := hP.sin_pos ht
  -- a non-tie point where the `t`-line is active and the cap has positive height
  have hAvol : volume (actU ω Θ h t ∩ posU ω Θ h) ≠ 0 := by
    intro h0
    rw [sigmaH, measureReal_def, h0] at hσ
    simp at hσ
  have hne : ((actU ω Θ h t ∩ posU ω Θ h) \ tieAll ω Θ h).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hemp
    exact hAvol (measure_mono_null (sdiff_eq_empty.1 hemp) (volume_tieAll hP h))
  obtain ⟨x₀, ⟨hx₀U, hx₀P⟩, hx₀T⟩ := hne
  have hactive : roofU ω Θ h x₀ = lineFn t (h t) x₀ := hx₀U
  have hpos : floorF ω h x₀ < roofU ω Θ h x₀ := hx₀P
  have hgap : ∀ s ∈ diamondFin ω Θ, s ≠ t → lineFn t (h t) x₀ < lineFn s (h s) x₀ := by
    intro s hs hst
    refine lt_of_le_of_ne ?_ (lineFn_ne_00 hx₀T ht hs (Ne.symm hst))
    rw [← hactive, roofU]
    exact Finset.inf'_le _ hs
  set δ := ((diamondFin ω Θ).erase t).inf' (erase_nonempty hP t)
    (fun s => lineFn s (h s) x₀ - lineFn t (h t) x₀) * sin t with hδ
  have hδpos : 0 < δ := by
    refine mul_pos ?_ hsin
    rw [show (0 : ℝ) = (0 : ℝ) from rfl, Finset.lt_inf'_iff]
    intro s hs
    obtain ⟨hst, hsD⟩ := Finset.mem_erase.1 hs
    linarith [hgap s hsD hst]
  refine ⟨δ, hδpos, fun ε hε => ?_⟩
  obtain ⟨hε0, hεδ⟩ := hε
  set p : ℝ² := pt x₀ (lineFn t (h t + ε) x₀) with hp
  have hp0 : p 0 = x₀ := by rw [hp, pt_zero]
  have hp1 : p 1 = lineFn t (h t) x₀ + ε / sin t := by
    rw [hp, pt_one, lineFn_add]
  refine ⟨p, (mem_capH_iff hP).2 ⟨fun s hs => ?_, fun s hs => ?_⟩, ?_⟩
  · -- lower constraints
    rw [← lineFn_le_iff (hP.sin_pos_fan hs), hp0, hp1]
    by_cases hst : s = t
    · subst hst
      rw [pushH_apply, if_pos rfl, show h s + ε - 1 = (h s - 1) + ε by ring, lineFn_add]
      have : lineFn s (h s - 1) x₀ ≤ lineFn s (h s) x₀ :=
        lineFn_mono (hP.sin_pos_fan hs) (by linarith) x₀
      linarith
    · rw [pushH_apply, if_neg hst, add_zero]
      have h1 : lineFn s (h s - 1) x₀ ≤ floorF ω h x₀ :=
        Finset.le_sup' (fun s => lineFn s (h s - 1) x₀) hs
      have h2 : 0 ≤ ε / sin t := div_nonneg hε0.le hsin.le
      rw [hactive] at hpos
      linarith
  · -- upper constraints
    rw [← le_lineFn_iff (hP.sin_pos hs), hp0, hp1]
    by_cases hst : s = t
    · subst hst
      rw [pushH_apply, if_pos rfl, show h s + ε = h s + ε by rfl, lineFn_add]
    · rw [pushH_apply, if_neg hst, add_zero]
      have hle : ε / sin t ≤ lineFn s (h s) x₀ - lineFn t (h t) x₀ := by
        rw [div_le_iff₀ hsin]
        refine hεδ.trans ?_
        rw [hδ]
        exact mul_le_mul_of_nonneg_right
          (Finset.inf'_le _ (Finset.mem_erase.2 ⟨hst, hs⟩)) hsin.le
      linarith
  · rw [inner_u_decomp, hp, pt_zero, pt_one, lineFn, div_mul_cancel₀ _ hsin.ne']
    ring

/-! ### The corner points of `o_ω` -/

omit hP in
lemma inner_oω_pi_div_two (ω : ℝ) : ⟪oω ω, u (π / 2)⟫ = 1 := by
  rw [inner_u_pi_div_two, oω, pt_one]

omit hP in
lemma inner_oω_ω (hP : PolySetup ω Θ) : ⟪oω ω, u ω⟫ = 1 := by
  rw [inner_u_decomp, oω, pt_zero, pt_one, one_mul]
  by_cases hω : ω = π / 2
  · rw [hω, cos_pi_div_two, sin_pi_div_two]; simp
  · have hc : 0 < cos ω :=
      cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hP.pos], lt_of_le_of_ne hP.le hω⟩
    field_simp
    ring

omit hP in
lemma inner_oω_zero (ω : ℝ) : ⟪oω ω, u 0⟫ = (1 - sin ω) / cos ω := by
  rw [inner_u_zero, oω, pt_zero]

omit hP in
lemma inner_oω_left (hP : PolySetup ω Θ) : ⟪oω ω, u (ω + π / 2)⟫ = (1 - sin ω) / cos ω := by
  rw [u_add_pi_div_two, inner_eq, oω, pt_zero, pt_one, v_coord_zero, v_coord_one, one_mul]
  by_cases hω : ω = π / 2
  · rw [hω, cos_pi_div_two, sin_pi_div_two]; simp
  · have hc : 0 < cos ω :=
      cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hP.pos], lt_of_le_of_ne hP.le hω⟩
    field_simp
    linear_combination sin_sq_add_cos_sq ω

/-- Points of the cap stay in the pushed cap provided they are high enough in direction `u_t`. -/
lemma mem_capH_push (hK : IsPolyCap ω Θ K) {t ε : ℝ} (hε0 : 0 ≤ ε) {p : ℝ²} (hp : p ∈ K)
    (hlow : t ∈ fanFin ω → ε ≤ ⟪p, u t⟫) : p ∈ capH ω Θ (pushH (supportFn K) t ε) := by
  refine (mem_capH_iff hP).2 ⟨fun s hs => ?_, fun s hs => ?_⟩
  · rw [pushH_apply]
    by_cases hst : s = t
    · subst hst
      rw [if_pos rfl]
      have h1 : supportFn K s = 1 := by
        rcases mem_fanFin.1 hs with hs' | hs' <;> rw [hs']
        exacts [hK.1.supportFn_ω, hK.1.supportFn_pi_div_two]
      rw [h1]
      have := hlow hs
      linarith
    · rw [if_neg hst, add_zero]
      have h1 : supportFn K s = 1 := by
        rcases mem_fanFin.1 hs with hs' | hs' <;> rw [hs']
        exacts [hK.1.supportFn_ω, hK.1.supportFn_pi_div_two]
      rw [h1, sub_self]
      rcases mem_fanFin.1 hs with hs' | hs' <;> rw [hs']
      · exact (hK.1.subset_fan hp).2
      · rw [inner_u_pi_div_two]; exact (hK.1.subset_fan hp).1
  · rw [pushH_apply]
    have := hK.1.inner_le hp s
    by_cases hst : s = t
    · rw [if_pos hst]; linarith
    · rw [if_neg hst]; linarith

/-- **Lemma 3.4.8 + Prop 3.3.7.** After pushing the `t`-line out by a small `ε > 0` we still
get a polygon cap, whose area functional dominates `A_Θ(h⁺)`. -/
theorem exists_isPolyCap_push (hK : IsPolyCap ω Θ K) (hoω : oω ω ∈ K) {t : ℝ}
    (ht : t ∈ diamondFin ω Θ) (hσ : 0 < sigmaH ω Θ (supportFn K) t) :
    ∃ δ > 0, ∀ ε ∈ Ioo 0 δ, ∃ K₀, IsPolyCap ω Θ K₀ ∧
      areaH ω Θ hP.nonempty (pushH (supportFn K) t ε) ≤ polySofaArea ω Θ K₀ := by
  set h := supportFn K with hh
  have hfan1 : ∀ s ∈ fanFin ω, h s = 1 := by
    intro s hs
    rcases mem_fanFin.1 hs with hs' | hs' <;> rw [hs', hh]
    exacts [hK.1.supportFn_ω, hK.1.supportFn_pi_div_two]
  obtain ⟨δ₀, hδ₀, htop⟩ := exists_top_point_push hP hK ht hσ
  set c : ℝ := if ω = π / 2 then 1 else 1 - sin ω with hc
  have hcpos : 0 < c := by
    rw [hc]
    by_cases hω : ω = π / 2
    · rw [if_pos hω]; norm_num
    · rw [if_neg hω]
      have : sin ω < 1 := by
        have := sin_lt_sin_of_lt_of_le_pi_div_two (x := ω) (y := π / 2)
          (by linarith [pi_pos, hP.pos]) le_rfl (lt_of_le_of_ne hP.le hω)
        rwa [sin_pi_div_two] at this
      linarith
  refine ⟨min δ₀ (min 1 c), lt_min hδ₀ (lt_min one_pos hcpos), fun ε hε => ?_⟩
  obtain ⟨hε0, hεlt⟩ := hε
  have hεδ₀ : ε ≤ δ₀ := le_of_lt (lt_of_lt_of_le hεlt (min_le_left _ _))
  have hε1 : ε ≤ 1 := le_of_lt (lt_of_lt_of_le hεlt ((min_le_right _ _).trans (min_le_left _ _)))
  have hεc : ε ≤ c := le_of_lt (lt_of_lt_of_le hεlt ((min_le_right _ _).trans (min_le_right _ _)))
  set hplus := pushH h t ε with hplus_def
  -- (A): the four supporting lines are touched
  have hA : ∀ s ∈ fanFin ω, ∃ p ∈ capH ω Θ hplus, ⟪p, u s⟫ = hplus s := by
    intro s hs
    by_cases hst : s = t
    · subst hst
      obtain ⟨p, hp, hps⟩ := htop ε ⟨hε0, hεδ₀⟩
      exact ⟨p, hp, by rw [hps, hplus_def, pushH_apply, if_pos rfl]⟩
    · refine ⟨oω ω, mem_capH_push hP hK hε0.le hoω fun htf => ?_, ?_⟩
      · rcases mem_fanFin.1 htf with ht' | ht' <;> rw [ht']
        · rw [inner_oω_ω hP]; exact hε1
        · rw [inner_oω_pi_div_two]; exact hε1
      · rw [hplus_def, pushH_apply, if_neg hst, add_zero]
        rw [hfan1 s hs]
        rcases mem_fanFin.1 hs with hs' | hs' <;> rw [hs']
        · exact inner_oω_ω hP
        · exact inner_oω_pi_div_two ω
  -- (B): the four lower lines are touched
  have hB : ∀ s ∈ fanFin ω, ∃ p ∈ capH ω Θ hplus, ⟪p, u s⟫ = hplus s - 1 := by
    intro s hs
    by_cases hst : s = t
    · -- the pushed bottom line: take a point of `K` at height `ε` in direction `u_t`
      subst hst
      have hs1 : h s = 1 := hfan1 s hs
      obtain ⟨q₁, hq₁, hq₁s⟩ := exists_supportFn_eq hK.1.isCompact hK.1.nonempty s
      obtain ⟨q₀, hq₀, hq₀s⟩ : ∃ q ∈ K, ⟪q, u s⟫ = 0 := by
        rcases mem_fanFin.1 hs with hs' | hs'
        · obtain ⟨q, hq, hqs⟩ := exists_supportFn_eq hK.1.isCompact hK.1.nonempty (ω + π)
          refine ⟨q, hq, ?_⟩
          rw [hs', ← neg_eq_zero, ← inner_neg_right, ← u_add_pi, hqs, hK.1.supportFn_ω_add_pi]
        · obtain ⟨q, hq, hqs⟩ := exists_supportFn_eq hK.1.isCompact hK.1.nonempty (3 * π / 2)
          refine ⟨q, hq, ?_⟩
          rw [hs', ← neg_eq_zero, ← inner_neg_right, ← u_three_pi_div_two, hqs,
            hK.1.supportFn_three_pi_div_two]
      set q := (1 - ε) • q₀ + ε • q₁ with hq_def
      have hqK : q ∈ K := hK.1.convex hq₀ hq₁ (by linarith) hε0.le (by ring)
      have hqs : ⟪q, u s⟫ = ε := by
        rw [hq_def, inner_add_left, real_inner_smul_left, real_inner_smul_left, hq₀s, hq₁s,
          ← hh, hs1]
        ring
      refine ⟨q, mem_capH_push hP hK hε0.le hqK fun _ => by rw [hqs], ?_⟩
      rw [hplus_def, pushH_apply, if_pos rfl, hs1, hqs]
      ring
    · -- the other fan line is untouched: use the corresponding corner of `K`
      have hs1 : h s = 1 := hfan1 s hs
      have hω : ω ≠ π / 2 ∨ t ∉ fanFin ω := by
        by_cases hωπ : ω = π / 2
        · refine Or.inr fun htf => hst ?_
          rcases mem_fanFin.1 hs with hs' | hs' <;> rcases mem_fanFin.1 htf with ht' | ht' <;>
            simp [hs', ht', hωπ]
        · exact Or.inl hωπ
      have hcos : ω ≠ π / 2 → c = 1 - sin ω := by
        intro hωπ; rw [hc, if_neg hωπ]
      have hlow : ∀ (p : ℝ²), p ∈ K → (t ∈ fanFin ω → ε ≤ ⟪p, u t⟫) →
          ⟪p, u s⟫ = 0 → ∃ p ∈ capH ω Θ hplus, ⟪p, u s⟫ = hplus s - 1 := by
        intro p hpK hpt hps
        refine ⟨p, mem_capH_push hP hK hε0.le hpK hpt, ?_⟩
        rw [hplus_def, pushH_apply, if_neg hst, add_zero, hs1, hps]
        ring
      rcases mem_fanFin.1 hs with hs' | hs'
      · -- `s = ω`: use the left corner `C`
        refine hlow hK.1.cornerC (hK.1.cornerC_mem hP.pos hP.le) (fun htf => ?_) ?_
        · -- then `t = π/2` and `ω < π/2`
          have hts : t = π / 2 := by
            rcases mem_fanFin.1 htf with ht' | ht'
            · exact absurd (hs'.trans ht'.symm) hst
            · exact ht'
          have hωπ : ω ≠ π / 2 := by
            rcases hω with hω | hω
            · exact hω
            · exact absurd htf hω
          have hcω : 0 < cos ω :=
            cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hP.pos], lt_of_le_of_ne hP.le hωπ⟩
          have hCle : (1 - sin ω) / cos ω ≤ supportFn K (ω + π / 2) := by
            rw [← inner_oω_left hP]
            exact hK.1.inner_le hoω (ω + π / 2)
        
          have : ⟪hK.1.cornerC, u (π / 2)⟫ = supportFn K (ω + π / 2) * cos ω := by
            rw [IsCap.cornerC, real_inner_smul_left, inner_v_u_eq_sin]
            congr 1
            rw [show π / 2 - ω = -(ω - π / 2) by ring, sin_neg, sin_sub, sin_pi_div_two,
              cos_pi_div_two]
            ring
          rw [hts, this]
          have h2 : 1 - sin ω ≤ supportFn K (ω + π / 2) * cos ω := by
            rw [div_le_iff₀ hcω] at hCle
            linarith
          have := hcos hωπ
          linarith
        · rw [hs', IsCap.cornerC, real_inner_smul_left, inner_v_u, mul_zero]
      · -- `s = π/2`: use the right corner `A`
        refine hlow hK.1.cornerA (hK.1.cornerA_mem hP.pos hP.le) (fun htf => ?_) ?_
        · have hts : t = ω := by
            rcases mem_fanFin.1 htf with ht' | ht'
            · exact ht'
            · exact absurd (hs'.trans ht'.symm) hst
          have hωπ : ω ≠ π / 2 := by
            rcases hω with hω | hω
            · exact hω
            · exact absurd htf hω
          have hcω : 0 < cos ω :=
            cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hP.pos], lt_of_le_of_ne hP.le hωπ⟩
          have hAle : (1 - sin ω) / cos ω ≤ supportFn K 0 := by
            rw [← inner_oω_zero ω]
            exact hK.1.inner_le hoω 0
          have hAval : ⟪hK.1.cornerA, u ω⟫ = supportFn K 0 * cos ω := by
            rw [IsCap.cornerA, real_inner_smul_left, inner_u_u_eq_cos, zero_sub, cos_neg]
          rw [hts, hAval]
          have h2 : 1 - sin ω ≤ supportFn K 0 * cos ω := by
            rw [div_le_iff₀ hcω] at hAle
            linarith
          have := hcos hωπ
          linarith
        · rw [hs', IsCap.cornerA, real_inner_smul_left, inner_u_u_eq_cos, zero_sub, cos_neg,
            cos_pi_div_two, mul_zero]
  -- translate so that the two widths are again `1`
  set a := hplus ω - 1 with ha
  set b := if ω = π / 2 then (0 : ℝ) else ((hplus (π / 2) - 1) - a * sin ω) / cos ω with hb
  set w : ℝ² := a • u ω + b • v ω with hw
  have hw1 : ⟪w, u ω⟫ = a := by
    rw [hw, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u_eq_cos,
      inner_v_u, sub_self, cos_zero]
    ring
  have hw2 : ⟪w, u (π / 2)⟫ = hplus (π / 2) - 1 := by
    have e1 : cos (ω - π / 2) = sin ω := by rw [cos_sub, cos_pi_div_two, sin_pi_div_two]; ring
    have e2 : sin (π / 2 - ω) = cos ω := by rw [sin_sub, sin_pi_div_two, cos_pi_div_two]; ring
    rw [hw, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u_eq_cos,
      inner_v_u_eq_sin, e1, e2]
    by_cases hωπ : ω = π / 2
    · rw [hb, if_pos hωπ, ha, hωπ]
      simp
    · have hcω : 0 < cos ω :=
        cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hP.pos], lt_of_le_of_ne hP.le hωπ⟩
      rw [hb, if_neg hωπ]
      field_simp
      ring
  set h₀ := transH hplus (-w) with h₀_def
  have h₀_apply : ∀ s, h₀ s = hplus s - ⟪w, u s⟫ := by
    intro s
    rw [h₀_def, transH, inner_neg_left]
    ring
  have h₀ω : h₀ ω = 1 := by rw [h₀_apply, hw1, ha]; ring
  have h₀π : h₀ (π / 2) = 1 := by rw [h₀_apply, hw2]; ring
  have hmemiff : ∀ q : ℝ², q - w ∈ capH ω Θ h₀ ↔ q ∈ capH ω Θ hplus := by
    intro q
    rw [h₀_def, capH_transH hP, mem_preimage, sub_neg_eq_add, sub_add_cancel]
  have hA₀ : ∀ s ∈ fanFin ω, ∃ p ∈ capH ω Θ h₀, ⟪p, u s⟫ = h₀ s := by
    intro s hs
    obtain ⟨q, hq, hqs⟩ := hA s hs
    exact ⟨q - w, (hmemiff q).2 hq, by rw [inner_sub_left, hqs, h₀_apply]⟩
  have hB₀ : ∀ s ∈ fanFin ω, ∃ p ∈ capH ω Θ h₀, ⟪p, u s⟫ = h₀ s - 1 := by
    intro s hs
    obtain ⟨q, hq, hqs⟩ := hB s hs
    exact ⟨q - w, (hmemiff q).2 hq, by rw [inner_sub_left, hqs, h₀_apply]; ring⟩
  have hpoly : IsPolyCap ω Θ (capH ω Θ h₀) := isPolyCap_capH hP h₀ω h₀π hA₀ hB₀
  refine ⟨capH ω Θ h₀, hpoly, ?_⟩
  rw [polySofaArea_eq_areaH hP hpoly.1]
  calc areaH ω Θ hP.nonempty hplus = areaH ω Θ hP.nonempty h₀ := by
        rw [h₀_def, areaH_transH hP]
    _ ≤ areaH ω Θ hP.nonempty (supportFn (capH ω Θ h₀)) :=
        areaH_le_areaH_supportFn hP h₀ω h₀π hpoly

/-- `τ(t) ≥ 0` for a polygon cap (uses the gap theorem 2.5.5 through `posR ⊆ posU`). -/
lemma tauH_nonneg (hK : IsPolyCap ω Θ K) {t : ℝ} (ht : t ∈ diamondFin ω Θ) :
    0 ≤ tauH ω Θ hP.nonempty (supportFn K) t := by
  set h := supportFn K with hh
  have hsub : actF ω h t ∩ posR ω Θ hP.nonempty h ⊆ actF ω h t ∩ posU ω Θ h :=
    inter_subset_inter_right _ (posR_subset_posU hP hK)
  have hfin : volume (actF ω h t ∩ posU ω Θ h) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_posU_ne_top hP h) (measure_mono inter_subset_right)
  have h1 := measureReal_mono hsub hfin
  have h2 : (0 : ℝ) ≤ volume.real (actR Θ hP.nonempty h t ∩ posR ω Θ hP.nonempty h) :=
    measureReal_nonneg
  rw [tauH]
  exact div_nonneg (by linarith) (hP.sin_pos ht).le

/-- **Theorem 3.4.9.** A maximum polygon cap is balanced. -/
theorem IsMaxPolyCap.balanced (hK : IsMaxPolyCap ω Θ K) {t : ℝ} (ht : t ∈ diamondFin ω Θ) :
    sigmaH ω Θ (supportFn K) t = tauH ω Θ hP.nonempty (supportFn K) t := by
  by_contra hne
  set h := supportFn K with hh
  obtain ⟨t', ht', hlt⟩ := exists_tauH_lt_sigmaH hP h ⟨t, ht, hne⟩
  have hτ : 0 ≤ tauH ω Θ hP.nonempty h t' := tauH_nonneg hP hK.1 ht'
  have hσ : 0 < sigmaH ω Θ h t' := lt_of_le_of_lt hτ hlt
  -- a positive derivative gives a strict increase for small `ε > 0`
  have hderiv := hasDerivAt_areaH_push hP h ht'
  have hslope := hasDerivAt_iff_tendsto_slope.1 hderiv
  have hposd : (0 : ℝ) < sigmaH ω Θ h t' - tauH ω Θ hP.nonempty h t' := by linarith
  have hev := hslope.eventually_const_lt hposd
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ₁, hδ₁, hball⟩ := hev
  obtain ⟨δ₂, hδ₂, hpoly⟩ := exists_isPolyCap_push hP hK.1 hK.2.1 ht' hσ
  set ε := min δ₁ δ₂ / 2 with hε
  have hε0 : 0 < ε := by
    rw [hε]
    exact half_pos (lt_min hδ₁ hδ₂)
  have hε1 : ε < δ₁ := by
    rw [hε]
    have := min_le_left δ₁ δ₂
    linarith
  have hε2 : ε < δ₂ := by
    rw [hε]
    have := min_le_right δ₁ δ₂
    linarith
  -- strict increase
  have hincr : areaH ω Θ hP.nonempty h < areaH ω Θ hP.nonempty (pushH h t' ε) := by
    have hd : dist ε 0 < δ₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hε0]
      exact hε1
    have hslopepos := hball hd (by simpa using hε0.ne')
    rw [slope_def_field, pushH_zero] at hslopepos
    have hdiv : 0 < (areaH ω Θ hP.nonempty (pushH h t' ε) - areaH ω Θ hP.nonempty h) / ε := by
      simpa [sub_zero, div_eq_inv_mul, mul_comm] using hslopepos
    have := (div_pos_iff.1 hdiv)
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · linarith
    · linarith
  -- contradiction with maximality
  obtain ⟨K₀, hK₀, hK₀area⟩ := hpoly ε ⟨hε0, hε2⟩
  have hmax := hK.2.2 K₀ hK₀
  rw [polySofaArea_eq_areaH hP hK.1.1, ← hh] at hmax
  linarith

end Push

/-! ## Theorem 3.4.10: a balanced maximum polygon cap contains its niche -/

section Contains

variable (hP : PolySetup ω Θ) {K : Set ℝ²}

variable (ω Θ) in
/-- The lower boundary of `F_ω ∖ N_Θ(h)`: the upper envelope of fan floor and niche roof. -/
def gfn (hΘ : Θ.Nonempty) (h : ℝ → ℝ) (x : ℝ) : ℝ := max (floorF ω h x) (roofR Θ hΘ h x)

omit hP in
lemma continuous_gfn (hΘ : Θ.Nonempty) (h : ℝ → ℝ) : Continuous (gfn ω Θ hΘ h) :=
  (continuous_floorF h).max (continuous_roofR hΘ h)

include hP in
lemma selection_gfn (h : ℝ → ℝ) (x : ℝ) :
    ∃ s ∈ diamondFin ω Θ, x ∈ activeSet (gfn ω Θ hP.nonempty h) (famA1 h) famBs s := by
  rcases max_choice (floorF ω h x) (roofR Θ hP.nonempty h x) with hm | hm
  · obtain ⟨s, hs, he⟩ := floorF_mem (ω := ω) h x
    refine ⟨s, mem_diamondFin_of_fan hs, ?_⟩
    show gfn ω Θ hP.nonempty h x = famA1 h s + famBs s * x
    rw [famA1_add, gfn, hm, he]
  · obtain ⟨r, hr, -, he⟩ := roofR_mem' hP h x
    refine ⟨r, hr, ?_⟩
    show gfn ω Θ hP.nonempty h x = famA1 h r + famBs r * x
    rw [famA1_add, gfn, hm, he]

omit hP in
lemma measure_eq_of_sdiff_eq {S S' T : Set ℝ} (hT : volume T = 0) (hSS : S \ T = S' \ T) :
    volume S = volume S' := by
  rw [← measure_sdiff_null (s := S) hT, ← measure_sdiff_null (s := S') hT, hSS]

include hP in
/-- The active sets of `g` inside `I` have measure `τ(s) sin s`. -/
theorem measureReal_activeSet_gfn (hK : IsPolyCap ω Θ K) {s : ℝ} (hs : s ∈ diamondFin ω Θ) :
    volume.real (activeSet (gfn ω Θ hP.nonempty (supportFn K)) (famA1 (supportFn K)) famBs s ∩
        posU ω Θ (supportFn K)) =
      tauH ω Θ hP.nonempty (supportFn K) s * sin s := by
  set h := supportFn K with hh
  set g := gfn ω Θ hP.nonempty h with hg
  set A := activeSet g (famA1 h) famBs s with hA
  set T := tieAll ω Θ h with hT
  have hTnull : volume T = 0 := volume_tieAll hP h
  have hRU := posR_subset_posU hP hK
  -- the set identity off the tie set
  have hkey : (A ∩ posU ω Θ h) \ T =
      ((actR Θ hP.nonempty h s ∩ posR ω Θ hP.nonempty h) ∪
        ((actF ω h s ∩ posU ω Θ h) \ posR ω Θ hP.nonempty h)) \ T := by
    ext x
    constructor
    · rintro ⟨⟨hxA, hxU⟩, hxT⟩
      refine ⟨?_, hxT⟩
      by_cases hxR : x ∈ posR ω Θ hP.nonempty h
      · refine Or.inl ⟨?_, hxR⟩
        have hmax : g x = roofR Θ hP.nonempty h x := max_eq_right (le_of_lt hxR)
        show roofR Θ hP.nonempty h x = lineFn s (h s - 1) x
        rw [← hmax, ← famA1_add]
        exact hxA
      · refine Or.inr ⟨⟨?_, hxU⟩, hxR⟩
        have hlt : roofR Θ hP.nonempty h x < floorF ω h x := by
          rcases lt_or_gt_of_ne (roofR_ne_floorF hP hxT) with hlt | hlt
          · exact hlt
          · exact absurd hlt hxR
        have hmax : g x = floorF ω h x := max_eq_left hlt.le
        show floorF ω h x = lineFn s (h s - 1) x
        rw [← hmax, ← famA1_add]
        exact hxA
    · rintro ⟨hx, hxT⟩
      refine ⟨⟨?_, ?_⟩, hxT⟩
      · rcases hx with ⟨hxR, hxP⟩ | ⟨⟨hxF, hxU⟩, hxP⟩
        · have hmax : g x = roofR Θ hP.nonempty h x := max_eq_right (le_of_lt hxP)
          show g x = famA1 h s + famBs s * x
          rw [famA1_add, hmax]
          exact hxR
        · have hlt : roofR Θ hP.nonempty h x < floorF ω h x := by
            rcases lt_or_gt_of_ne (roofR_ne_floorF hP hxT) with hlt | hlt
            · exact hlt
            · exact absurd hlt hxP
          have hmax : g x = floorF ω h x := max_eq_left hlt.le
          show g x = famA1 h s + famBs s * x
          rw [famA1_add, hmax]
          exact hxF
      · rcases hx with ⟨-, hxP⟩ | ⟨⟨-, hxU⟩, -⟩
        · exact hRU hxP
        · exact hxU
  have hmeas := measure_eq_of_sdiff_eq hTnull hkey
  -- compute the measure of the right-hand side
  have hdisj : Disjoint (actR Θ hP.nonempty h s ∩ posR ω Θ hP.nonempty h)
      ((actF ω h s ∩ posU ω Θ h) \ posR ω Θ hP.nonempty h) :=
    Set.disjoint_left.2 fun x hx hx' => hx'.2 hx.2
  have hm1 : MeasurableSet ((actF ω h s ∩ posU ω Θ h) \ posR ω Θ hP.nonempty h) :=
    (((isClosed_actF (ω := ω) h s).measurableSet).inter
      (measurableSet_posU h)).diff (measurableSet_posR hP h)
  have hfinU : volume (actF ω h s ∩ posU ω Θ h) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_posU_ne_top hP h) (measure_mono inter_subset_right)
  have hfinR : volume (actR Θ hP.nonempty h s ∩ posR ω Θ hP.nonempty h) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_posR_ne_top hP h) (measure_mono inter_subset_right)
  have hsub : actF ω h s ∩ posR ω Θ hP.nonempty h ⊆ actF ω h s ∩ posU ω Θ h :=
    inter_subset_inter_right _ hRU
  have hinter : (actF ω h s ∩ posU ω Θ h) ∩ posR ω Θ hP.nonempty h =
      actF ω h s ∩ posR ω Θ hP.nonempty h := by
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, hRU hx.2⟩, hx.2⟩⟩
  have hsetdiff : (actF ω h s ∩ posU ω Θ h) \ posR ω Θ hP.nonempty h =
      (actF ω h s ∩ posU ω Θ h) \ (actF ω h s ∩ posR ω Θ hP.nonempty h) := by
    ext x
    constructor
    · rintro ⟨hx, hxR⟩
      exact ⟨hx, fun hc => hxR hc.2⟩
    · rintro ⟨hx, hxR⟩
      exact ⟨hx, fun hc => hxR ⟨hx.1, hc⟩⟩
  have hfinR' : volume (actF ω h s ∩ posR ω Θ hP.nonempty h) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_posR_ne_top hP h) (measure_mono inter_subset_right)
  have hdiff : volume ((actF ω h s ∩ posU ω Θ h) \ posR ω Θ hP.nonempty h) =
      volume (actF ω h s ∩ posU ω Θ h) - volume (actF ω h s ∩ posR ω Θ hP.nonempty h) := by
    rw [hsetdiff, measure_sdiff hsub (((isClosed_actF (ω := ω) h s).measurableSet).inter
      (measurableSet_posR hP h)).nullMeasurableSet hfinR']
  have hfin2 : volume (actF ω h s ∩ posU ω Θ h) -
      volume (actF ω h s ∩ posR ω Θ hP.nonempty h) ≠ ⊤ := ne_top_of_le_ne_top hfinU tsub_le_self
  rw [measureReal_def, hmeas, measure_union hdisj hm1, hdiff, tauH,
    div_mul_cancel₀ _ (hP.sin_pos hs).ne', ENNReal.toReal_add hfinR hfin2,
    ENNReal.toReal_sub_of_le (measure_mono hsub) hfinU]
  simp only [measureReal_def]
  ring

include hP in
lemma posU_subset_Ioi (hK : IsPolyCap ω Θ K) :
    posU ω Θ (supportFn K) ⊆ Ioi (-(supportFn K (ω + π / 2) * sin ω)) := by
  have hsω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hP.pos (by linarith [pi_pos, hP.le])
  have hcω : 0 ≤ cos ω := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos, hP.pos], hP.le⟩
  have hmem : ∀ x ∈ posU ω Θ (supportFn K),
      -(supportFn K (ω + π / 2) * sin ω) ≤ x := by
    intro x hx
    have hx' : floorF ω (supportFn K) x < roofU ω Θ (supportFn K) x := hx
    set y := (floorF ω (supportFn K) x + roofU ω Θ (supportFn K) x) / 2 with hy
    have hp : pt x y ∈ capH ω Θ (supportFn K) := by
      constructor <;> simp only [pt_zero, pt_one, hy] <;> linarith
    rw [capH_supportFn hP hK] at hp
    have h1 : 0 ≤ ⟪pt x y, u ω⟫ := (hK.1.subset_fan hp).2
    have h2 : ⟪pt x y, u (ω + π / 2)⟫ ≤ supportFn K (ω + π / 2) := hK.1.inner_le hp _
    have h3 : pt x y 0 = cos ω * ⟪pt x y, u ω⟫ - sin ω * ⟪pt x y, u (ω + π / 2)⟫ := by
      rw [inner_u_decomp, inner_u_decomp, cos_add_pi_div_two, sin_add_pi_div_two]
      linear_combination (-(pt x y 0)) * sin_sq_add_cos_sq ω
    rw [pt_zero] at h3
    nlinarith [mul_le_mul_of_nonneg_left h2 hsω.le, mul_nonneg hcω h1]
  intro x hx
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isOpen_posU (ω := ω) (Θ := Θ) (supportFn K)) x hx
  have hmem' : x - δ / 2 ∈ posU ω Θ (supportFn K) := by
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, show x - δ / 2 - x = -(δ / 2) by ring, abs_neg,
      abs_of_pos (by linarith)]
    linarith
  have := hmem _ hmem'
  simp only [mem_Ioi]
  linarith

include hP in
lemma posU_eq_Ioo (hK : IsPolyCap ω Θ K) :
    posU ω Θ (supportFn K) = Ioo (-(supportFn K (ω + π / 2) * sin ω)) (supportFn K 0) :=
  subset_antisymm (fun _ hx => ⟨posU_subset_Ioi hP hK hx, posU_subset_Iio hP hK hx⟩)
    (Ioo_subset_posU hP hK)

include hP in
lemma gfn_eq_roofU_right (hK : IsPolyCap ω Θ K) :
    gfn ω Θ hP.nonempty (supportFn K) (supportFn K 0) =
      roofU ω Θ (supportFn K) (supportFn K 0) := by
  set h := supportFn K with hh
  have hA : hK.1.cornerA ∈ capH ω Θ h := by
    rw [capH_supportFn hP hK]
    exact hK.1.cornerA_mem hP.pos hP.le
  have hAx : hK.1.cornerA 0 = h 0 := by rw [hK.1.cornerA_eq, pt_zero]
  have hAy : hK.1.cornerA 1 = 0 := by rw [hK.1.cornerA_eq, pt_one]
  have h1 : floorF ω h (h 0) ≤ roofU ω Θ h (h 0) := by
    have := hA.1
    have := hA.2
    rw [hAx, hAy] at *
    linarith
  have h2 : roofU ω Θ h (h 0) ≤ floorF ω h (h 0) := by
    by_contra hcon
    push Not at hcon
    have hmem : h 0 ∈ posU ω Θ h := hcon
    have hlt := posU_subset_Iio hP hK hmem
    rw [mem_Iio, ← hh] at hlt
    exact lt_irrefl _ hlt
  have h3 : roofR Θ hP.nonempty h (h 0) ≤ floorF ω h (h 0) := by
    by_contra hcon
    push Not at hcon
    have hmem : h 0 ∈ posR ω Θ hP.nonempty h := hcon
    have hlt := posU_subset_Iio hP hK (posR_subset_posU hP hK hmem)
    rw [mem_Iio, ← hh] at hlt
    exact lt_irrefl _ hlt
  rw [gfn, max_eq_left h3]
  linarith

/-- **Theorem 3.4.10.** A balanced polygon cap contains its polygon niche. -/
theorem polyNiche_subset_of_balanced (hK : IsPolyCap ω Θ K)
    (hbal : ∀ s ∈ diamondFin ω Θ,
      sigmaH ω Θ (supportFn K) s = tauH ω Θ hP.nonempty (supportFn K) s) :
    polyNiche ω Θ K ⊆ K := by
  set h := supportFn K with hh
  set b := h 0 with hb
  set g := gfn ω Θ hP.nonempty h with hg
  have hcontg : Continuous g := continuous_gfn hP.nonempty h
  have hselg := selection_gfn hP h
  have hselU := selection_roofU (ω := ω) (Θ := Θ) h
  have hdist1 := affDistinct1 hP h
  have hdist0 := affDistinct0 hP h
  -- the key inequality `g ≤ U` on `I`
  have key : ∀ x ∈ posU ω Θ h, g x ≤ roofU ω Θ h x := by
    intro x hx
    rw [roofU, Finset.le_inf'_iff]
    intro s₀ hs₀
    -- an edge point of `K` for the angle `s₀`
    obtain ⟨q, hqK, hq⟩ := exists_supportFn_eq hK.1.isCompact hK.1.nonempty s₀
    set xs := q 0 with hxs
    have hxsb : xs ≤ b := by
      have := hK.1.inner_le hqK 0
      rwa [inner_u_zero] at this
    have hqline : q 1 = lineFn s₀ (h s₀) xs := by
      have h1 : q 1 ≤ lineFn s₀ (h s₀) xs := by
        rw [← hh] at hq
        exact (le_lineFn_iff (hP.sin_pos hs₀) (h s₀) q).2 (le_of_eq hq)
      have h2 : lineFn s₀ (h s₀) xs ≤ q 1 := by
        rw [← hh] at hq
        exact (lineFn_le_iff (hP.sin_pos hs₀) (h s₀) q).2 (ge_of_eq hq)
      linarith
    have hUxs : roofU ω Θ h xs = lineFn s₀ (h s₀) xs := by
      refine le_antisymm (Finset.inf'_le _ hs₀) ?_
      have hqcap : q ∈ capH ω Θ h := by rw [capH_supportFn hP hK]; exact hqK
      rw [← hqline]
      exact hqcap.2
    have hxb : x < b := posU_subset_Iio hP hK hx
    -- FTC for `g` on `[x, b]` and for `U` on `[xs, b]`
    have hftcg := sub_eq_sum_mul_measureReal_activeSet hdist1 hcontg hselg hxb.le
    have hftcU := sub_eq_sum_mul_measureReal_activeSet hdist0
      (continuous_roofU (ω := ω) (Θ := Θ) h) hselU hxsb
    have hpartg := sum_measureReal_activeSet_inter hdist1 hcontg hselg
      (measurableSet_Icc (a := x) (b := b)) measure_Icc_lt_top.ne
    have hpartU := sum_measureReal_activeSet_inter hdist0
      (continuous_roofU (ω := ω) (Θ := Θ) h) hselU
      (measurableSet_Icc (a := xs) (b := b)) measure_Icc_lt_top.ne
    rw [Real.volume_real_Icc, max_eq_left (by linarith : (0:ℝ) ≤ b - x)] at hpartg
    rw [Real.volume_real_Icc, max_eq_left (by linarith : (0:ℝ) ≤ b - xs)] at hpartU
    -- termwise comparison of the two sums
    have hterm : ∀ s ∈ diamondFin ω Θ,
        (famBs s - famBs s₀) *
            volume.real (activeSet (roofU ω Θ h) (famA0 h) famBs s ∩ Icc xs b) ≤
          (famBs s - famBs s₀) *
            volume.real (activeSet g (famA1 h) famBs s ∩ Icc x b) := by
      intro s hs
      rcases lt_trichotomy (famBs s) (famBs s₀) with hlt | heq | hgt
      · -- `s < s₀`: the whole `g`-piece fits into the `U`-piece
        have hsubU : actU ω Θ h s ∩ posU ω Θ h ⊆ Icc xs b := by
          rintro y ⟨hyU, hyP⟩
          refine ⟨?_, le_of_lt (posU_subset_Iio hP hK hyP)⟩
          have e1 : lineFn s (h s) y ≤ lineFn s₀ (h s₀) y := by
            have : roofU ω Θ h y = lineFn s (h s) y := hyU
            rw [← this, roofU]
            exact Finset.inf'_le _ hs₀
          have e2 : lineFn s₀ (h s₀) xs ≤ lineFn s (h s) xs := by
            rw [← hUxs, roofU]
            exact Finset.inf'_le _ hs
          rw [← famA0_add, ← famA0_add] at e1 e2
          nlinarith [e1, e2, hlt]
        have hsubg : activeSet g (famA1 h) famBs s ∩ Icc x b ⊆
            (activeSet g (famA1 h) famBs s ∩ posU ω Θ h) ∪ {b} := by
          rintro y ⟨hyg, hy1, hy2⟩
          rcases eq_or_lt_of_le hy2 with rfl | hy3
          · exact Or.inr rfl
          · refine Or.inl ⟨hyg, ?_⟩
            rw [posU_eq_Ioo hP hK] at hx ⊢
            exact ⟨lt_of_lt_of_le hx.1 hy1, hy3⟩
        have hfin1 : volume (activeSet g (famA1 h) famBs s ∩ posU ω Θ h) ≠ ⊤ :=
          ne_top_of_le_ne_top (volume_posU_ne_top hP h) (measure_mono inter_subset_right)
        have hcg : volume.real (activeSet g (famA1 h) famBs s ∩ Icc x b) ≤
            volume.real (activeSet g (famA1 h) famBs s ∩ posU ω Θ h) := by
          have hle : volume (activeSet g (famA1 h) famBs s ∩ Icc x b) ≤
              volume (activeSet g (famA1 h) famBs s ∩ posU ω Θ h) := by
            calc volume (activeSet g (famA1 h) famBs s ∩ Icc x b)
                ≤ volume ((activeSet g (famA1 h) famBs s ∩ posU ω Θ h) ∪ {b}) :=
                  measure_mono hsubg
              _ ≤ volume (activeSet g (famA1 h) famBs s ∩ posU ω Θ h) +
                    volume ({b} : Set ℝ) := measure_union_le (μ := volume) _ _
              _ = volume (activeSet g (famA1 h) famBs s ∩ posU ω Θ h) := by
                  rw [Real.volume_singleton, add_zero]
          exact ENNReal.toReal_mono hfin1 hle
        have hcU : volume.real (actU ω Θ h s ∩ posU ω Θ h) ≤
            volume.real (activeSet (roofU ω Θ h) (famA0 h) famBs s ∩ Icc xs b) := by
          rw [← actU_eq]
          refine measureReal_mono (subset_inter inter_subset_left hsubU) ?_
          exact ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono inter_subset_right)
        have hkey : volume.real (activeSet g (famA1 h) famBs s ∩ Icc x b) ≤
            volume.real (activeSet (roofU ω Θ h) (famA0 h) famBs s ∩ Icc xs b) := by
          refine le_trans hcg (le_trans (le_of_eq ?_) hcU)
          rw [measureReal_activeSet_gfn hP hK hs, ← hbal s hs, sigmaH,
            div_mul_cancel₀ _ (hP.sin_pos hs).ne']
        nlinarith [hkey, hlt]
      · -- `s = s₀`
        rw [heq]
        simp
      · -- `s > s₀`: the `U`-piece is a single point
        have hzero : volume.real (activeSet (roofU ω Θ h) (famA0 h) famBs s ∩ Icc xs b) = 0 := by
          have hsub : activeSet (roofU ω Θ h) (famA0 h) famBs s ∩ Icc xs b ⊆ {xs} := by
            rintro y ⟨hyU, hy1, -⟩
            have hyU' : roofU ω Θ h y = lineFn s (h s) y := by
              have hy' : y ∈ actU ω Θ h s := by rw [actU_eq]; exact hyU
              exact hy'
            have e1 : lineFn s (h s) y ≤ lineFn s₀ (h s₀) y := by
              rw [← hyU', roofU]
              exact Finset.inf'_le _ hs₀
            have e2 : lineFn s₀ (h s₀) xs ≤ lineFn s (h s) xs := by
              rw [← hUxs, roofU]
              exact Finset.inf'_le _ hs
            rw [← famA0_add, ← famA0_add] at e1 e2
            have : y ≤ xs := by nlinarith [e1, e2, hgt]
            exact le_antisymm this hy1
          have hmono : volume (activeSet (roofU ω Θ h) (famA0 h) famBs s ∩ Icc xs b) ≤
              volume ({xs} : Set ℝ) := measure_mono hsub
          rw [Real.volume_singleton] at hmono
          simp only [measureReal_def]
          exact (ENNReal.toReal_eq_zero_iff _).2 (Or.inl (le_antisymm hmono bot_le))
        rw [hzero, mul_zero]
        exact mul_nonneg (by linarith) measureReal_nonneg
    have hsum := Finset.sum_le_sum hterm
    have hexp : ∀ c : ℝ → ℝ, ∑ s ∈ diamondFin ω Θ, (famBs s - famBs s₀) * c s
        = (∑ s ∈ diamondFin ω Θ, famBs s * c s) - famBs s₀ * ∑ s ∈ diamondFin ω Θ, c s := by
      intro c
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    have hgb : g b = roofU ω Θ h b := by
      rw [hg, hb, hh]
      exact gfn_eq_roofU_right hP hK
    rw [hexp, hexp, ← hftcg, ← hftcU, hpartg, hpartU, hUxs, ← famA0_add, hgb] at hsum
    rw [← famA0_add]
    linarith
  -- conclude
  intro p hp
  rw [polyNiche_eq_nicheH hP hK.1] at hp
  obtain ⟨hlow, hlt⟩ := hp
  have hxR : p 0 ∈ posR ω Θ hP.nonempty h := lt_of_le_of_lt hlow hlt
  have hxU := posR_subset_posU hP hK hxR
  have hkey := key (p 0) hxU
  rw [← capH_supportFn hP hK]
  refine ⟨hlow, ?_⟩
  have : roofR Θ hP.nonempty h (p 0) ≤ g (p 0) := le_max_right _ _
  linarith

end Contains

end Sofa
