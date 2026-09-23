/-
# Sofa/PolyCap.lean — polygon caps and balanced maximum caps (Baek §3.2, Def 3.4.1, §3.5)

Definitions (statement level) for Chapter 3:
* angle sets `Θ` (Def 3.2.1) as finite subsets of `(0, ω)`, `Θ^⋄` (Def 3.2.2);
* polygon caps `IsPolyCap ω Θ K` (Def 3.2.3), `C_Θ(K)` (Def 3.2.4), polygon niche `N_Θ(K)`
  (Def 3.2.5, **with the fan `F_ω`** — see blueprint risk R14), `A_Θ` (Def 3.2.6);
* maximum polygon caps (Def 3.4.1), uniform angle sets (Def 3.5.1), balanced maximum caps
  (Def 3.5.2);
* elementary facts: `K ⊆ C_Θ(K)`, `N_Θ(K) ⊆ N(K)`, boundedness of niches, and **Thm 3.2.3**
  (`A_ω(K) ≤ A_Θ(K)`).

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 1 (2026-09-17, Opus 5): compiled in the cloud dev tree
(Lean 4.33.1, Mathlib v4.33.1 with subset imports), no `sorry`; full `import Mathlib` re-check pending.
-/
import Sofa.CapThm

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²} {ω : ℝ}

/-! ## Definitions -/

/-- **Def 3.2.1.** An angle set with rotation angle `ω`: a nonempty finite subset of `(0, ω)`. -/
def IsAngleSet (ω : ℝ) (Θ : Finset ℝ) : Prop := Θ.Nonempty ∧ ∀ t ∈ Θ, 0 < t ∧ t < ω

/-- **Def 3.2.2.** `Θ^⋄ = Θ ∪ (Θ + π/2) ∪ {ω, π/2}`. -/
def diamondAngles (ω : ℝ) (Θ : Finset ℝ) : Set ℝ :=
  (Θ : Set ℝ) ∪ ((· + π / 2) '' (Θ : Set ℝ)) ∪ {ω, π / 2}

/-- The admissible normal angles of a polygon cap: `Θ^⋄ ∪ {ω + π, 3π/2}`. -/
def polyCapAngles (ω : ℝ) (Θ : Finset ℝ) : Set ℝ := diamondAngles ω Θ ∪ {ω + π, 3 * π / 2}

/-- **Def 3.2.3.** A polygon cap with angle set `Θ`. -/
def IsPolyCap (ω : ℝ) (Θ : Finset ℝ) (K : Set ℝ²) : Prop :=
  IsCap K ω ∧ K = ⋂ t ∈ polyCapAngles ω Θ, hpLe t (supportFn K t)

/-- **Def 3.2.4.** `C_Θ(K) = P_ω ∩ ⋂_{t ∈ Θ} Q⁺_K(t)`. -/
def polyCap (ω : ℝ) (Θ : Finset ℝ) (K : Set ℝ²) : Set ℝ² :=
  para ω ∩ ⋂ t ∈ Θ, QplusS K t

/-- **Def 3.2.5** (fan version, see risk R14). `N_Θ(K) = F_ω ∩ ⋃_{t ∈ Θ} Q⁻_K(t)`. -/
def polyNiche (ω : ℝ) (Θ : Finset ℝ) (K : Set ℝ²) : Set ℝ² :=
  fan ω ∩ ⋃ t ∈ Θ, QminusS K t

/-- **Def 3.2.6.** The polygon sofa area functional `A_Θ(K) = |C_Θ(K)| - |N_Θ(K)|`. -/
def polySofaArea (ω : ℝ) (Θ : Finset ℝ) (K : Set ℝ²) : ℝ :=
  (volume (polyCap ω Θ K)).toReal - (volume (polyNiche ω Θ K)).toReal

/-- The upper right vertex `o_ω = (tan (π/4 - ω/2), 1)` of `P_ω` (Def 2.3.5); for `ω = π/2` the
formula gives `(0, 1)` (Lean's `0 / 0 = 0`). -/
def oω (ω : ℝ) : ℝ² := pt ((1 - sin ω) / cos ω) 1

/-- **Def 3.4.1.** A maximum polygon cap with angle set `Θ`. -/
def IsMaxPolyCap (ω : ℝ) (Θ : Finset ℝ) (K : Set ℝ²) : Prop :=
  IsPolyCap ω Θ K ∧ oω ω ∈ K ∧
    ∀ K', IsPolyCap ω Θ K' → polySofaArea ω Θ K' ≤ polySofaArea ω Θ K

/-- **Def 3.5.1.** The uniform angle set `Θ_{ω,n} = {iω/n : 1 ≤ i < n}`. -/
def uniformAngles (ω : ℝ) (n : ℕ) : Finset ℝ :=
  (Finset.Ioo 0 n).image fun i : ℕ => (i : ℝ) * ω / n

/-- **Def 3.5.2.** A balanced maximum cap: a Hausdorff limit of maximum polygon caps with uniform
angle sets of `n_i` steps, `1 < n_1 < n_2 < …` powers of two. -/
def IsBalancedMaxCap (K : Set ℝ²) (ω : ℝ) : Prop :=
  IsCap K ω ∧ ∃ (n : ℕ → ℕ) (Ks : ℕ → Set ℝ²), StrictMono n ∧
    (∀ i, 1 < n i ∧ ∃ k : ℕ, n i = 2 ^ k) ∧
    (∀ i, IsMaxPolyCap ω (uniformAngles ω (n i)) (Ks i)) ∧
    Tendsto (fun i => Metric.hausdorffDist (Ks i) K) atTop (𝓝 0)

/-! ## Elementary facts -/

lemma uniformAngles_isAngleSet (hω : 0 < ω) {n : ℕ} (hn : 1 < n) :
    IsAngleSet ω (uniformAngles ω n) := by
  refine ⟨⟨(1 : ℕ) * ω / n, Finset.mem_image.2 ⟨1, Finset.mem_Ioo.2 ⟨one_pos, hn⟩, rfl⟩⟩, ?_⟩
  intro t ht
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ht
  obtain ⟨hi0, hin⟩ := Finset.mem_Ioo.1 hi
  have hn' : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans hn)
  have hi0' : (0 : ℝ) < i := by exact_mod_cast hi0
  have hin' : (i : ℝ) < n := by exact_mod_cast hin
  refine ⟨by positivity, ?_⟩
  rw [div_lt_iff₀ hn', mul_comm]
  exact mul_lt_mul_of_pos_left hin' hω

lemma subset_polyCap (hK : IsCap K ω) (Θ : Finset ℝ) : K ⊆ polyCap ω Θ K := by
  intro p hp
  refine ⟨hK.subset_para hp, mem_iInter₂.2 fun t _ => ?_⟩
  exact ⟨hK.inner_le hp t, hK.inner_le hp (t + π / 2)⟩

lemma polyNiche_subset_niche {Θ : Finset ℝ} (hΘ : IsAngleSet ω Θ) (K : Set ℝ²) :
    polyNiche ω Θ K ⊆ niche K ω := by
  rintro p ⟨hF, hp⟩
  rw [mem_iUnion₂] at hp
  obtain ⟨t, ht, hQ⟩ := hp
  exact mem_niche_iff.2 ⟨hF, t, hΘ.2 t ht, hQ⟩

lemma isClosed_polyCap (ω : ℝ) (Θ : Finset ℝ) (K : Set ℝ²) : IsClosed (polyCap ω Θ K) :=
  (isClosed_para ω).inter (isClosed_biInter fun t _ => isClosed_QplusS K t)

lemma abs_supportFn_le {S : Set ℝ²} (hS : IsCompact S) (hne : S.Nonempty) {R : ℝ}
    (hR : ∀ p ∈ S, ‖p‖ ≤ R) (t : ℝ) : |supportFn S t| ≤ R := by
  have hu : ∀ p : ℝ², |⟪p, u t⟫| ≤ ‖p‖ := fun p => by
    have := abs_real_inner_le_norm p (u t); rwa [norm_u, mul_one] at this
  rw [abs_le]
  constructor
  · obtain ⟨p, hp⟩ := hne
    have h1 := le_supportFn hS hp t
    have h2 := hu p
    have h3 := hR p hp
    rw [abs_le] at h2
    linarith [h2.1]
  · rw [supportFn_le_iff hS hne]
    intro p hp
    exact (le_abs_self _).trans ((hu p).trans (hR p hp))

/-- Points of a polygon-cap-like set `P_ω ∩ Q⁺_K(t)` are bounded. -/
lemma isBounded_polyCap (hω1 : ω ≤ π / 2) {Θ : Finset ℝ} (hΘ : IsAngleSet ω Θ) (K : Set ℝ²) :
    Bornology.IsBounded (polyCap ω Θ K) := by
  obtain ⟨t, ht⟩ := hΘ.1
  obtain ⟨ht0, ht1⟩ := hΘ.2 t ht
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 (by linarith [pi_pos])
  have hc : 0 < cos t := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  refine isBounded_iff_forall_norm_le.2
    ⟨(|supportFn K t| / cos t + |supportFn K (t + π / 2)| / sin t) + 1, fun p hp => ?_⟩
  have hH : 0 ≤ p 1 ∧ p 1 ≤ 1 := hp.1.1
  have hQ := (mem_iInter₂.1 hp.2) t ht
  rw [mem_QplusS_iff, u_add_pi_div_two, inner_eq, inner_eq, u_coord_zero, u_coord_one,
    v_coord_zero, v_coord_one] at hQ
  refine norm_le_add_of_abs_coord_le ?_ (abs_le.2 ⟨by linarith [hH.1], hH.2⟩)
  have hA := le_abs_self (supportFn K t)
  have hB := le_abs_self (supportFn K (t + π / 2))
  have hA' := div_nonneg (abs_nonneg (supportFn K t)) hc.le
  have hB' := div_nonneg (abs_nonneg (supportFn K (t + π / 2))) hs.le
  rw [abs_le]
  constructor
  · have e1 : -|supportFn K (t + π / 2)| ≤ p 0 * sin t := by
      nlinarith [mul_nonneg hH.1 hc.le]
    have e2 : -|supportFn K (t + π / 2)| / sin t ≤ p 0 := by
      rw [div_le_iff₀ hs]; exact e1
    rw [neg_div] at e2
    linarith
  · have e1 : p 0 * cos t ≤ |supportFn K t| := by
      nlinarith [mul_nonneg hH.1 hs.le]
    have e2 : p 0 ≤ |supportFn K t| / cos t := by
      rw [le_div_iff₀ hc]; exact e1
    linarith

namespace IsCap

variable (hK : IsCap K ω) (hω0 : 0 < ω) (hω1 : ω ≤ π / 2)
include hK hω0 hω1

/-- Wedge points lie strictly between the two corners in the `x`-direction. -/
lemma coord_zero_bounds_of_mem_wedge {t : ℝ} (ht : t ∈ Ioo 0 ω) {p : ℝ²}
    (hp : p ∈ wedge K ω t) : hK.cornerC 0 < p 0 ∧ p 0 < hK.cornerA 0 := by
  obtain ⟨⟨hp1, hpω⟩, hQ⟩ := hp
  rw [mem_QminusS_iff, u_add_pi_div_two] at hQ
  obtain ⟨hs, hc, -, hsw, hcw, -⟩ := trig_facts ht hω1
  constructor
  · have hZ := hK.gapZ_pos hω1 ht
    rw [gapZ, sub_pos, div_lt_iff₀ hcw] at hZ
    have hsinω : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
    have e1 : ⟪p, v t⟫ = -(p 0) * sin t + p 1 * cos t := by
      simp only [inner_eq, v_coord_zero, v_coord_one]; ring
    have e2 := inner_u_decomp p ω
    have e3 : cos (ω - t) = cos ω * cos t + sin ω * sin t := cos_sub ω t
    have hC0e : hK.cornerC 0 = -(supportFn K (ω + π / 2) * sin ω) := by
      simp [cornerC, v]
    rw [hC0e]
    have iden : (p 0 + supportFn K (ω + π / 2) * sin ω) * cos (ω - t) - cos t * ⟪p, u ω⟫ =
        sin ω * (supportFn K (ω + π / 2) * cos (ω - t) - ⟪p, v t⟫) := by
      rw [e1, e2, e3]; ring
    have key : 0 < (p 0 + supportFn K (ω + π / 2) * sin ω) * cos (ω - t) := by
      nlinarith [mul_nonneg hc.le hpω, mul_pos hsinω (by linarith : 0 <
        supportFn K (ω + π / 2) * cos (ω - t) - ⟪p, v t⟫)]
    have := pos_of_mul_pos_left key hcw.le
    linarith
  · have hW := hK.gapW_pos hω1 ht
    rw [gapW, sub_pos, div_lt_iff₀ hc] at hW
    have e := inner_u_decomp p t
    rw [hK.cornerA_eq, pt_zero]
    have key : p 0 * cos t < supportFn K 0 * cos t := by
      nlinarith [mul_nonneg hp1 hs.le]
    exact lt_of_mul_lt_mul_right key hc.le

/-- The niche of a cap is bounded. -/
theorem isBounded_niche : Bornology.IsBounded (niche K ω) := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hK.isCompact.isBounded
  have hh : ∀ s, |supportFn K s| ≤ R := abs_supportFn_le hK.isCompact hK.nonempty hR
  refine isBounded_iff_forall_norm_le.2
    ⟨(|hK.cornerA 0| + |hK.cornerC 0|) + (2 * R + 2), fun p hp => ?_⟩
  rw [niche_eq_iUnion_wedge, mem_iUnion₂] at hp
  obtain ⟨t, ht, hpt⟩ := hp
  obtain ⟨h0l, h0r⟩ := hK.coord_zero_bounds_of_mem_wedge hω0 hω1 ht hpt
  obtain ⟨⟨hp1, -⟩, hQ⟩ := hpt
  rw [mem_QminusS_iff, u_add_pi_div_two] at hQ
  obtain ⟨hs, hc, hs1, -, -, -⟩ := trig_facts ht hω1
  have hc1 : cos t ≤ 1 := cos_le_one t
  have e := coord_one_decomp p t
  have hA := abs_le.1 (hh t)
  have hB := abs_le.1 (hh (t + π / 2))
  refine norm_le_add_of_abs_coord_le ?_ ?_
  · rw [abs_le]
    constructor
    · linarith [neg_abs_le (hK.cornerC 0), abs_nonneg (hK.cornerA 0)]
    · linarith [le_abs_self (hK.cornerA 0), abs_nonneg (hK.cornerC 0)]
  · rw [abs_le]
    constructor
    · linarith
    · have h1 : ⟪p, u t⟫ * sin t ≤ (R + 1) * 1 := by
        rcases le_or_gt 0 ⟪p, u t⟫ with h | h
        · exact mul_le_mul (by linarith) hs1.le hs.le (by linarith)
        · nlinarith
      have h2 : ⟪p, v t⟫ * cos t ≤ (R + 1) * 1 := by
        rcases le_or_gt 0 ⟪p, v t⟫ with h | h
        · exact mul_le_mul (by linarith) hc1 hc.le (by linarith)
        · nlinarith
      linarith

/-- **Theorem 3.2.3** (second half): `A_ω(K) ≤ A_Θ(K)` for every cap `K`. -/
theorem sofaArea_le_polySofaArea {Θ : Finset ℝ} (hΘ : IsAngleSet ω Θ) :
    sofaArea K ω ≤ polySofaArea ω Θ K := by
  have hC : volume (polyCap ω Θ K) ≠ ⊤ := (isBounded_polyCap hω1 hΘ K).measure_lt_top.ne
  have hN : volume (niche K ω) ≠ ⊤ := (hK.isBounded_niche hω0 hω1).measure_lt_top.ne
  have h1 : (volume K).toReal ≤ (volume (polyCap ω Θ K)).toReal :=
    ENNReal.toReal_mono hC (measure_mono (subset_polyCap hK Θ))
  have h2 : (volume (polyNiche ω Θ K)).toReal ≤ (volume (niche K ω)).toReal :=
    ENNReal.toReal_mono hN (measure_mono (polyNiche_subset_niche hΘ K))
  rw [sofaArea, polySofaArea]
  linarith

end IsCap

end Sofa
