/-
# Sofa/PolyGap.lean — the normal set of a polygon cap, and its gaps

The §6.4 machinery of `Sofa/GapArm.lean` and `Sofa/GapSum.lean` takes a *finite* normal set
`A : Finset ℝ` with `K = ⋂_{r ∈ A} H_K(r)` and an interval `(a, b)` that avoids all of the
directions `u_r`, `r ∈ A`.  For a polygon cap the normal set is
`Θ^⋄ ∪ {ω+π, 3π/2} = Θ ∪ (Θ + π/2) ∪ {ω, π/2, ω+π, 3π/2}` (Def 3.2.2–3.2.3), which this file
packages as a `Finset` (`polyCapFin`), and for the uniform angle set `Θ_{π/2,n} = {iδ}` the two
families of gaps that Theorem 6.4.3 needs are

* `(jδ, (j+1)δ)`        — between consecutive angles, used for `σ_K((jδ, (j+1)δ]) = σ_K({(j+1)δ})`;
* `(jδ + π/2, (j+1)δ + π/2)` — its `π/2`-shift, used for the Lipschitz bound on `g⁺_K`.

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.ArmBound
import Sofa.BalancedMax
import Sofa.GapSum

noncomputable section

open Real Set Filter Topology MeasureTheory Metric
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

/-! ## Distinct directions -/

/-- Two angles strictly less than `2π` apart point in different directions. -/
lemma u_ne_u_of_sub_lt {r s : ℝ} (h1 : -(2 * π) < r - s) (h2 : r - s < 2 * π) (hne : r ≠ s) :
    u r ≠ u s := by
  intro h
  have hcos : cos (r - s) = 1 := by
    rw [← inner_u_u_eq_cos, h, inner_u_u_eq_cos, sub_self, cos_zero]
  exact hne (by linarith [(Real.cos_eq_one_iff_of_lt_of_lt h1 h2).1 hcos])

/-! ## The normal set of a polygon cap as a `Finset` -/

/-- `Θ^⋄ ∪ {ω+π, 3π/2}` as a `Finset`. -/
def polyCapFin (ω : ℝ) (Θ : Finset ℝ) : Finset ℝ :=
  (Θ ∪ Θ.image (· + π / 2)) ∪ {ω, π / 2, ω + π, 3 * π / 2}

lemma mem_polyCapFin {ω : ℝ} {Θ : Finset ℝ} {r : ℝ} :
    r ∈ polyCapFin ω Θ ↔
      r ∈ Θ ∨ (∃ q ∈ Θ, r = q + π / 2) ∨ r = ω ∨ r = π / 2 ∨ r = ω + π ∨ r = 3 * π / 2 := by
  simp only [polyCapFin, Finset.mem_union, Finset.mem_image, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ((h | ⟨q, hq, rfl⟩) | h | h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨q, hq, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rintro (h | ⟨q, hq, rfl⟩ | h | h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨q, hq, rfl⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

lemma coe_polyCapFin (ω : ℝ) (Θ : Finset ℝ) :
    (↑(polyCapFin ω Θ) : Set ℝ) = polyCapAngles ω Θ := by
  ext r
  simp only [Finset.mem_coe, mem_polyCapFin, polyCapAngles, diamondAngles, Set.mem_union,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro (h | ⟨q, hq, rfl⟩ | h | h | h | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨q, hq, rfl⟩))
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (((h | ⟨q, hq, rfl⟩) | h | h) | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨q, hq, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- The half-plane representation of a polygon cap, indexed by a `Finset`. -/
theorem IsPolyCap.eq_iInter_fin {ω : ℝ} {Θ : Finset ℝ} {K : Set ℝ²} (hK : IsPolyCap ω Θ K) :
    K = ⋂ r ∈ polyCapFin ω Θ, hpLe r (supportFn K r) := by
  refine hK.2.trans ?_
  ext p
  simp only [Set.mem_iInter]
  constructor
  · intro hp r hr
    exact hp r (by rw [← coe_polyCapFin]; exact hr)
  · intro hp r hr
    exact hp r (by rw [← Finset.mem_coe, coe_polyCapFin]; exact hr)

/-! ## A maximum polygon cap has positive width in every direction -/

/-- A maximum polygon cap has area at least `1/4`: it beats the all-ones polygon cap
(`quarter_le_polySofaArea_one`), whose polygon sofa area is at least `1/4`, and the polygon sofa
area is dominated by the volume (`ofReal_le_volume_of_polySofaArea`). -/
theorem volume_ne_zero_of_isMaxPolyCap {ω : ℝ} {Θ : Finset ℝ} (hP : PolySetup ω Θ) {K : Set ℝ²}
    (hK : IsMaxPolyCap ω Θ K) : volume K ≠ 0 := by
  have harea : (1:ℝ) / 4 ≤ polySofaArea ω Θ K :=
    le_trans (quarter_le_polySofaArea_one hP) (hK.2.2 _ (isPolyCap_one hP))
  have hvol := ofReal_le_volume_of_polySofaArea hP hK.1 harea
  intro h0
  rw [h0, le_zero_iff, ENNReal.ofReal_eq_zero] at hvol
  norm_num at hvol

/-- Consequently the face lemma applies to a maximum polygon cap in *every* direction. -/
theorem width_pos_of_isMaxPolyCap {ω : ℝ} {Θ : Finset ℝ} (hP : PolySetup ω Θ) {K : Set ℝ²}
    (hK : IsMaxPolyCap ω Θ K) (s : ℝ) : 0 < supportFn K s + supportFn K (s + π) :=
  width_pos_of_volume_ne_zero hK.1.1.isCompact hK.1.1.nonempty
    (volume_ne_zero_of_isMaxPolyCap hP hK) s

/-! ## The gaps of a uniform angle set -/

section Uniform

variable {n : ℕ}

lemma mem_uniformAngles_iff {t : ℝ} :
    t ∈ uniformAngles (π / 2) n ↔ ∃ i : ℕ, 0 < i ∧ i < n ∧ t = (i : ℝ) * ((π / 2) / n) := by
  simp only [uniformAngles, Finset.mem_image, Finset.mem_Ioo]
  constructor
  · rintro ⟨i, ⟨hi0, hin⟩, rfl⟩
    exact ⟨i, hi0, hin, by ring⟩
  · rintro ⟨i, hi0, hin, rfl⟩
    exact ⟨i, ⟨hi0, hin⟩, by ring⟩

variable (hn : 1 < n)

include hn

private lemma cast_pos : (0:ℝ) < n := by
  exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn.le

private lemma step_pos : 0 < (π / 2) / n := by
  have := cast_pos hn
  have := pi_pos
  positivity

/-- **The gap between two consecutive angles** of `Θ_{π/2,n}` contains no normal direction of a
polygon cap with that angle set. -/
theorem uniform_gap_base {j : ℕ} (hj : j + 1 ≤ n) :
    ∀ s ∈ Ioo ((j : ℝ) * ((π / 2) / n)) (((j : ℝ) + 1) * ((π / 2) / n)),
      ∀ r ∈ polyCapFin (π / 2) (uniformAngles (π / 2) n), u r ≠ u s := by
  have hpi := pi_pos
  have hn0 := cast_pos hn
  have hδ0 := step_pos hn
  set δ : ℝ := (π / 2) / n with hδdef
  have hnδ : (n : ℝ) * δ = π / 2 := by rw [hδdef]; field_simp
  have hjn : ((j : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hj
  have hj0 : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  intro s hs r hr
  obtain ⟨hs1, hs2⟩ := hs
  have hs0 : 0 < s := lt_of_le_of_lt (by nlinarith) hs1
  have hsπ : s < π / 2 := by nlinarith
  rcases mem_polyCapFin.1 hr with hΘ | ⟨q, hq, rfl⟩ | rfl | rfl | rfl | rfl
  · obtain ⟨i, hi0, hin, rfl⟩ := mem_uniformAngles_iff.1 hΘ
    have hi0' : (0:ℝ) < (i : ℝ) := by exact_mod_cast hi0
    have hin' : (i : ℝ) < (n : ℝ) := by exact_mod_cast hin
    have hrπ : (i : ℝ) * δ < π / 2 := by nlinarith
    have hne : (i : ℝ) * δ ≠ s := by
      rcases le_or_gt i j with h | h
      · have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast h
        nlinarith
      · have : ((j : ℝ) + 1) ≤ (i : ℝ) := by exact_mod_cast h
        nlinarith
    exact u_ne_u_of_sub_lt (by nlinarith) (by nlinarith) hne
  · obtain ⟨i, hi0, hin, rfl⟩ := mem_uniformAngles_iff.1 hq
    have hi0' : (0:ℝ) < (i : ℝ) := by exact_mod_cast hi0
    have hin' : (i : ℝ) < (n : ℝ) := by exact_mod_cast hin
    have hrπ : (i : ℝ) * δ < π / 2 := by nlinarith
    exact u_ne_u_of_sub_lt (by nlinarith) (by nlinarith) (by nlinarith)
  · exact u_ne_u_of_sub_lt (by nlinarith) (by nlinarith) (by nlinarith)
  · exact u_ne_u_of_sub_lt (by nlinarith) (by nlinarith) (by nlinarith)
  · exact u_ne_u_of_sub_lt (by nlinarith) (by nlinarith) (by nlinarith)
  · exact u_ne_u_of_sub_lt (by nlinarith) (by nlinarith) (by nlinarith)

/-- **The `π/2`-shifted gap**, used for the Lipschitz bound of Lemma 6.4.1. -/
theorem uniform_gap_shift {j : ℕ} (hj : j + 1 ≤ n) :
    ∀ s ∈ Ioo ((j : ℝ) * ((π / 2) / n) + π / 2) (((j : ℝ) + 1) * ((π / 2) / n) + π / 2),
      ∀ r ∈ polyCapFin (π / 2) (uniformAngles (π / 2) n), u r ≠ u s := by
  have hpi := pi_pos
  have hn0 := cast_pos hn
  have hδ0 := step_pos hn
  set δ : ℝ := (π / 2) / n with hδdef
  have hnδ : (n : ℝ) * δ = π / 2 := by rw [hδdef]; field_simp
  have hjn : ((j : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hj
  have hj0 : (0:ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  intro s hs r hr
  obtain ⟨hs1, hs2⟩ := hs
  have hs0 : π / 2 < s := lt_of_le_of_lt (by nlinarith) hs1
  have hsπ : s < π := by nlinarith
  rcases mem_polyCapFin.1 hr with hΘ | ⟨q, hq, rfl⟩ | rfl | rfl | rfl | rfl
  · obtain ⟨i, hi0, hin, rfl⟩ := mem_uniformAngles_iff.1 hΘ
    have hi0' : (0:ℝ) < (i : ℝ) := by exact_mod_cast hi0
    have hin' : (i : ℝ) < (n : ℝ) := by exact_mod_cast hin
    have hrπ : (i : ℝ) * δ < π / 2 := by nlinarith
    exact u_ne_u_of_sub_lt (by nlinarith) (by nlinarith) (by nlinarith)
  · obtain ⟨i, hi0, hin, rfl⟩ := mem_uniformAngles_iff.1 hq
    have hi0' : (0:ℝ) < (i : ℝ) := by exact_mod_cast hi0
    have hin' : (i : ℝ) < (n : ℝ) := by exact_mod_cast hin
    have hrπ : (i : ℝ) * δ < π / 2 := by nlinarith
    have hne : (i : ℝ) * δ + π / 2 ≠ s := by
      rcases le_or_gt i j with h | h
      · have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast h
        nlinarith
      · have : ((j : ℝ) + 1) ≤ (i : ℝ) := by exact_mod_cast h
        nlinarith
    exact u_ne_u_of_sub_lt (by nlinarith) (by nlinarith) hne
  · exact u_ne_u_of_sub_lt (by nlinarith) (by nlinarith) (by nlinarith)
  · exact u_ne_u_of_sub_lt (by nlinarith) (by nlinarith) (by nlinarith)
  · exact u_ne_u_of_sub_lt (by nlinarith) (by nlinarith) (by nlinarith)
  · exact u_ne_u_of_sub_lt (by nlinarith) (by nlinarith) (by nlinarith)

/-! ## The one-step bound of Equation (6.4) -/

/-- **Baek Equation (6.4)** for a maximum polygon cap with the uniform angle set `Θ_{π/2,n}`:
combining Theorem 6.3.3 (`edgeLength_le_k0_delta`), the concentration of `σ_K` on the normals
(`sigmaK_Ioc_eq_singleton_of_gap` with `uniform_gap_base`) and Lemma 6.4.1
(`k0_armGp_mul_le_integral` with `uniform_gap_shift`),

    `σ_K((jδ, (j+1)δ]) ≤ ∫_{(j+1)δ}^{(j+2)δ} k₀(g⁺_K) + (6 + 4R) δ²`.  -/
theorem sigmaK_step_le_integral {K : Set ℝ²}
    (hK : IsMaxPolyCap (π / 2) (uniformAngles (π / 2) n) K)
    {R : ℝ} (hR : ∀ p ∈ K, ‖p‖ ≤ R) (hδ1 : (π / 2) / n ≤ 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j + 3 ≤ n) :
    (sigmaK K (Ioc ((j : ℝ) * ((π / 2) / n)) (((j : ℝ) + 1) * ((π / 2) / n)))).toReal
      ≤ (∫ r in (((j : ℝ) + 1) * ((π / 2) / n))..((((j : ℝ) + 1) * ((π / 2) / n)) + (π / 2) / n),
            k0 (armGp K r)) + (6 + 4 * R) * ((π / 2) / n) ^ 2 := by
  have hpi := pi_pos
  have hn0 := cast_pos hn
  have hδ0 := step_pos hn
  set δ : ℝ := (π / 2) / n with hδdef
  have hnδ : (n : ℝ) * δ = π / 2 := by rw [hδdef]; field_simp
  set t : ℝ := ((j : ℝ) + 1) * δ with htdef
  have hKc := hK.1.1.isCompact
  have hKne := hK.1.1.nonempty
  have hconv := hK.1.1.convex
  have hA := IsPolyCap.eq_iInter_fin hK.1
  have hP : PolySetup (π / 2) (uniformAngles (π / 2) n) :=
    ⟨by linarith, le_rfl, uniformAngles_isAngleSet (by linarith) hn⟩
  have hwidth := width_pos_of_isMaxPolyCap hP hK
  have hjn : (j : ℝ) + 3 ≤ (n : ℝ) := by exact_mod_cast hj2
  have hj1' : (1:ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  -- (1) the whole step mass sits at its right endpoint
  have h1 : sigmaK K (Ioc ((j : ℝ) * δ) t) = sigmaK K {t} :=
    sigmaK_Ioc_eq_singleton_of_gap hKc hKne hconv hA hwidth (by nlinarith)
      (uniform_gap_base hn (by omega))
  -- (2) Theorem 6.3.3
  have ht : t ∈ uniformAngles (π / 2) n :=
    mem_uniformAngles_iff.2 ⟨j + 1, by omega, by omega, by rw [htdef]; push_cast; ring⟩
  have htm : t - δ ∈ uniformAngles (π / 2) n :=
    mem_uniformAngles_iff.2 ⟨j, hj1, by omega, by rw [htdef]; ring⟩
  have htp : t + δ ∈ uniformAngles (π / 2) n :=
    mem_uniformAngles_iff.2 ⟨j + 2, by omega, by omega, by rw [htdef]; push_cast; ring⟩
  have ht0 : 0 < t - δ := by rw [htdef]; nlinarith
  have ht2 : t + δ < π / 2 := by rw [htdef, ← hnδ]; nlinarith
  have h3 := edgeLength_le_k0_delta hP hK hδ0 hδ1 ht0 ht2 ht htm htp
  -- (3) Lemma 6.4.1 on the shifted gap
  have hgapsh : ∀ s ∈ Ioo (t + π / 2) (t + δ + π / 2),
      ∀ r ∈ polyCapFin (π / 2) (uniformAngles (π / 2) n), u r ≠ u s := by
    have h := uniform_gap_shift hn (j := j + 1) (by omega)
    intro s hs r hr
    refine h s ?_ r hr
    have e1 : ((j + 1 : ℕ) : ℝ) * δ + π / 2 = t + π / 2 := by rw [htdef]; push_cast; ring
    have e2 : ((((j + 1 : ℕ) : ℝ) + 1)) * δ + π / 2 = t + δ + π / 2 := by
      rw [htdef]; push_cast; ring
    rw [e1, e2]
    exact hs
  have h4 := k0_armGp_mul_le_integral hKc hKne hconv hA hwidth hgapsh hR hδ0.le
    (t := t) (δ := δ) ⟨le_rfl, by linarith⟩ le_rfl
  -- (4) assemble
  have hk0le : k0 (armGp K t) ≤ 1 + 2 * R :=
    (k0_le_one_add_abs _).trans (by linarith [abs_armGp_le hKc hKne hR t])
  have hδsq : (0:ℝ) ≤ δ ^ 2 := sq_nonneg δ
  have htoReal : (sigmaK K (Ioc ((j : ℝ) * δ) t)).toReal = edgeLength K t := by
    rw [h1, sigmaK_singleton hKc hKne, ENNReal.toReal_ofReal (edgeLength_nonneg hKc hKne t)]
  rw [htoReal]
  nlinarith [h3, h4, hk0le, hδsq]

/-- **Baek Equation (6.5)** for a maximum polygon cap with the uniform angle set `Θ_{π/2,n}`:
summing Equation (6.4) over the steps `mδ, …, (m+N)δ` and shifting the integration window back,

    `σ_K((mδ, (m+N)δ]) ≤ ∫_{mδ}^{(m+N)δ} k₀(g⁺_K) + N(6+4R)δ² + (1+2R)δ`,

and `Nδ ≤ π/2`, so the whole error is `O(δ)`. -/
theorem sigmaK_Ioc_le_integral_poly {K : Set ℝ²}
    (hK : IsMaxPolyCap (π / 2) (uniformAngles (π / 2) n) K)
    {R : ℝ} (hR : ∀ p ∈ K, ‖p‖ ≤ R) (hδ1 : (π / 2) / n ≤ 1)
    {m N : ℕ} (hm : 1 ≤ m) (hmN : m + N + 2 ≤ n) :
    (sigmaK K (Ioc ((m : ℝ) * ((π / 2) / n)) (((m : ℝ) + N) * ((π / 2) / n)))).toReal
      ≤ (∫ r in ((m : ℝ) * ((π / 2) / n))..(((m : ℝ) + N) * ((π / 2) / n)), k0 (armGp K r))
        + ((N : ℝ) * ((6 + 4 * R) * ((π / 2) / n) ^ 2) + (1 + 2 * R) * ((π / 2) / n)) := by
  have hpi := pi_pos
  have hn0 := cast_pos hn
  have hδ0 := step_pos hn
  set δ : ℝ := (π / 2) / n with hδdef
  have hKc := hK.1.1.isCompact
  have hKne := hK.1.1.nonempty
  obtain ⟨p₀, hp₀⟩ := hKne
  have hR0 : (0:ℝ) ≤ R := le_trans (norm_nonneg p₀) (hR p₀ hp₀)
  set a : ℝ := (m : ℝ) * δ with hadef
  have hstep : ∀ j < N, (sigmaK K (Ioc (a + (j : ℕ) * δ) (a + ((j : ℕ) + 1) * δ))).toReal
      ≤ (∫ r in (a + ((j : ℕ) + 1) * δ)..(a + ((j : ℕ) + 2) * δ), k0 (armGp K r))
        + (6 + 4 * R) * δ ^ 2 := by
    intro j hj
    have h := sigmaK_step_le_integral hn hK hR hδ1 (j := m + j) (by omega) (by omega)
    rw [← hδdef] at h
    have e1 : ((m + j : ℕ) : ℝ) * δ = a + (j : ℕ) * δ := by rw [hadef]; push_cast; ring
    have e2 : (((m + j : ℕ) : ℝ) + 1) * δ = a + ((j : ℕ) + 1) * δ := by
      rw [hadef]; push_cast; ring
    have e3 : a + ((j : ℕ) + 1) * δ + δ = a + ((j : ℕ) + 2) * δ := by ring
    rw [e1, e2, e3] at h
    exact h
  have hmain := sigmaK_Ioc_le_integral_of_steps hKc ⟨p₀, hp₀⟩ hδ0.le N
    (show (0:ℝ) ≤ (6 + 4 * R) * δ ^ 2 by positivity) hstep
  have hshift := integral_k0_armGp_shift_le hKc ⟨p₀, hp₀⟩ hR (a := a) (b := a + (N : ℝ) * δ)
    (δ := δ) hδ0.le
  have e4 : a + ((N : ℝ) + 1) * δ = a + (N : ℝ) * δ + δ := by ring
  have e5 : a + (N : ℝ) * δ = ((m : ℝ) + N) * δ := by rw [hadef]; ring
  rw [e4] at hmain
  rw [e5] at hmain hshift
  linarith

end Uniform

/-! ## Theorem 6.4.3 on a dyadic interval -/

section Balanced

variable {K : Set ℝ²}

/-- **Baek Theorem 6.4.3** on an interval with dyadic endpoints.  `K` is a balanced maximum cap
(`ω = π/2`), so it is the Hausdorff limit of maximum polygon caps `K_i` with uniform angle sets of
`n_i` steps, `n_i` a strictly increasing sequence of powers of two.  A dyadic angle
`p·(π/2)/2^k` is a cut point of `Θ_{n_i}` for every `i` with `n_i ≥ 2^k`, so Equation (6.5)
applies with an error `O(δ_i) → 0`, and `sigmaK_Ioc_le_integral_of_limit'` takes the limit. -/
theorem sigmaK_Ioc_le_integral_dyadic (hK : IsBalancedMaxCap K (π / 2))
    {k p q : ℕ} (hp : 0 < p) (hqp : p ≤ q) (hq : q < 2 ^ k)
    {a b : ℝ} (hab : a ≤ b)
    (ha : (p : ℝ) * (π / 2) / 2 ^ k ≤ a) (hb : b ≤ (q : ℝ) * (π / 2) / 2 ^ k)
    (hda : edgeLength K a = 0) (hdb : edgeLength K b = 0) :
    (sigmaK K (Ioc a b)).toReal
      ≤ ∫ t in ((p : ℝ) * (π / 2) / 2 ^ k)..((q : ℝ) * (π / 2) / 2 ^ k), k0 (armGp K t) := by
  have hpi := pi_pos
  obtain ⟨hcap, n, Ks, hmono, hn2, hmax, hlim⟩ := hK
  have hKc := hcap.isCompact
  have hKne := hcap.nonempty
  have hKsc : ∀ i, IsCompact (Ks i) := fun i => (hmax i).1.1.isCompact
  have hKsne : ∀ i, (Ks i).Nonempty := fun i => (hmax i).1.1.nonempty
  obtain ⟨R, hR⟩ := exists_eventually_norm_le hKsc hKsne hKc hKne hlim
  set A : ℝ := (p : ℝ) * (π / 2) / 2 ^ k with hAdef
  set B : ℝ := (q : ℝ) * (π / 2) / 2 ^ k with hBdef
  set C : ℝ := (6 + 4 * R) * (π / 2) + (1 + 2 * R) with hCdef
  set err : ℕ → ℝ := fun i => C * ((π / 2) / (n i : ℝ)) with herrdef
  have hn_top : Tendsto (fun i => ((n i : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmono.tendsto_atTop
  have herr : Tendsto err atTop (𝓝 0) := by
    have hdiv : Tendsto (fun i => (π / 2) / ((n i : ℕ) : ℝ)) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds hn_top
    have := hdiv.const_mul C
    rwa [mul_zero] at this
  have hbound : ∀ᶠ i in atTop, (sigmaK (Ks i) (Ioc A B)).toReal
      ≤ (∫ t in A..B, k0 (armGp (Ks i) t)) + err i := by
    filter_upwards [hR, eventually_ge_atTop (2 ^ (k + 1))] with i hRi hik
    have hn1 : 1 < n i := (hn2 i).1
    have hni : 2 ^ (k + 1) ≤ n i := le_trans hik hmono.le_apply
    obtain ⟨ki, hki⟩ := (hn2 i).2
    have hkki : k + 1 ≤ ki := by
      have h2 : (2:ℕ) ^ (k + 1) ≤ 2 ^ ki := by rw [← hki]; exact hni
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
    set c : ℕ := 2 ^ (ki - k) with hcdef
    have hnc : n i = 2 ^ k * c := by
      rw [hki, hcdef, ← pow_add]
      congr 1
      omega
    have hc2 : 2 ≤ c := by
      rw [hcdef]
      calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (ki - k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    -- the indices
    set m : ℕ := p * c with hmdef
    set N : ℕ := (q - p) * c with hNdef
    have hm : 1 ≤ m := by rw [hmdef]; exact Nat.one_le_iff_ne_zero.2 (by positivity)
    have hmN : m + N + 2 ≤ n i := by
      rw [hmdef, hNdef, hnc]
      have hqc : q * c + 2 ≤ 2 ^ k * c := by
        have h1 : q + 1 ≤ 2 ^ k := hq
        nlinarith [hc2, Nat.zero_le q]
      calc p * c + (q - p) * c + 2 = q * c + 2 := by
            rw [← Nat.add_mul]; congr 2; omega
        _ ≤ 2 ^ k * c := hqc
    -- the geometry
    have hn0 : (0:ℝ) < (n i : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1.le
    have hc0 : (0:ℝ) < (c : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hc2
    have h2k0 : (0:ℝ) < (2:ℝ) ^ k := by positivity
    have hncR : ((n i : ℕ) : ℝ) = 2 ^ k * (c : ℝ) := by
      rw [hnc]; push_cast; ring
    have hδ1 : (π / 2) / ((n i : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hn0]
      have h2n : (2:ℝ) ≤ (n i : ℝ) := by exact_mod_cast hn1
      linarith [Real.pi_le_four]
    have hAeq : ((m : ℕ) : ℝ) * ((π / 2) / ((n i : ℕ) : ℝ)) = A := by
      rw [hAdef, hmdef, hncR]
      push_cast
      field_simp
    have hBeq : (((m : ℕ) : ℝ) + ((N : ℕ) : ℝ)) * ((π / 2) / ((n i : ℕ) : ℝ)) = B := by
      have hmn : ((m : ℕ) : ℝ) + ((N : ℕ) : ℝ) = (q : ℝ) * (c : ℝ) := by
        rw [hmdef, hNdef]
        push_cast [Nat.cast_sub hqp]
        ring
      rw [hmn, hBdef, hncR]
      field_simp
    have hmain := sigmaK_Ioc_le_integral_poly hn1 (hmax i) hRi hδ1 hm hmN
    rw [hAeq, hBeq] at hmain
    refine hmain.trans ?_
    -- the error bound
    have hR0 : (0:ℝ) ≤ R := by
      obtain ⟨z, hz⟩ := hKsne i
      exact le_trans (norm_nonneg z) (hRi z hz)
    have hδ0 : (0:ℝ) < (π / 2) / ((n i : ℕ) : ℝ) := by positivity
    have hNδ : ((N : ℕ) : ℝ) * ((π / 2) / ((n i : ℕ) : ℝ)) ≤ π / 2 := by
      have hNn : ((N : ℕ) : ℝ) ≤ ((n i : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ n i)
      have hpi2 : (0:ℝ) < π / 2 := by linarith
      rw [mul_div_assoc', div_le_iff₀ hn0]
      nlinarith
    have herri : err i
        = ((6 + 4 * R) * (π / 2) + (1 + 2 * R)) * ((π / 2) / ((n i : ℕ) : ℝ)) := by
      simp only [herrdef, hCdef]
    rw [herri]
    have hc : (0:ℝ) ≤ (6 + 4 * R) * ((π / 2) / ((n i : ℕ) : ℝ)) :=
      mul_nonneg (by linarith) hδ0.le
    have key : ((N : ℕ) : ℝ) * ((6 + 4 * R) * ((π / 2) / ((n i : ℕ) : ℝ)) ^ 2)
        ≤ (6 + 4 * R) * (π / 2) * ((π / 2) / ((n i : ℕ) : ℝ)) := by
      calc ((N : ℕ) : ℝ) * ((6 + 4 * R) * ((π / 2) / ((n i : ℕ) : ℝ)) ^ 2)
          = (6 + 4 * R) * ((π / 2) / ((n i : ℕ) : ℝ))
              * (((N : ℕ) : ℝ) * ((π / 2) / ((n i : ℕ) : ℝ))) := by ring
        _ ≤ (6 + 4 * R) * ((π / 2) / ((n i : ℕ) : ℝ)) * (π / 2) :=
            mul_le_mul_of_nonneg_left hNδ hc
        _ = (6 + 4 * R) * (π / 2) * ((π / 2) / ((n i : ℕ) : ℝ)) := by ring
    linarith
  exact sigmaK_Ioc_le_integral_of_limit' hKsc hKsne hKc hKne hlim hR hab ha hb hda hdb herr hbound

/-! ## Theorem 6.4.3 on an arbitrary interval of continuity points -/

/-- Dyadic angles are dense: a closed interval `[a, b] ⊂ (0, π/2)` can be sandwiched between two
dyadic multiples of `π/2` at distance `< ε`. -/
lemma exists_dyadic_sandwich {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hb2 : b < π / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ k p q : ℕ, 0 < p ∧ p ≤ q ∧ q < 2 ^ k ∧
      (p : ℝ) * (π / 2) / 2 ^ k ≤ a ∧ a - (p : ℝ) * (π / 2) / 2 ^ k < ε ∧
      b ≤ (q : ℝ) * (π / 2) / 2 ^ k ∧ (q : ℝ) * (π / 2) / 2 ^ k - b < ε := by
  have hpi := pi_pos
  have hL0 : (0:ℝ) < π / 2 := by positivity
  set α : ℝ := a / (π / 2) with hαdef
  set β : ℝ := b / (π / 2) with hβdef
  have hα0 : 0 < α := div_pos ha0 hL0
  have hβ0 : 0 < β := div_pos (lt_of_lt_of_le ha0 hab) hL0
  have hβ1 : β < 1 := (div_lt_one hL0).2 hb2
  have hαβ : α ≤ β := by rw [hαdef, hβdef]; gcongr
  have hcpos : 0 < min (ε / (π / 2)) (min α (1 - β)) := by
    refine lt_min (div_pos hε hL0) (lt_min hα0 (by linarith))
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hcpos (by norm_num : (1:ℝ) / 2 < 1)
  have hMpos : (0:ℝ) < 2 ^ k := by positivity
  have hkM : 1 / (2:ℝ) ^ k < min (ε / (π / 2)) (min α (1 - β)) := by
    rwa [div_pow, one_pow] at hk
  have hk1 : 1 / (2:ℝ) ^ k < ε / (π / 2) := lt_of_lt_of_le hkM (min_le_left _ _)
  have hk2 : 1 / (2:ℝ) ^ k < α := lt_of_lt_of_le hkM (le_trans (min_le_right _ _) (min_le_left _ _))
  have hk3 : 1 / (2:ℝ) ^ k < 1 - β :=
    lt_of_lt_of_le hkM (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨k, ⌊α * 2 ^ k⌋₊, ⌈β * 2 ^ k⌉₊, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_floor ?_)
    push_cast
    rw [div_lt_iff₀ hMpos] at hk2
    linarith
  · calc ⌊α * 2 ^ k⌋₊ ≤ ⌊β * 2 ^ k⌋₊ :=
        Nat.floor_le_floor (mul_le_mul_of_nonneg_right hαβ hMpos.le)
      _ ≤ ⌈β * 2 ^ k⌉₊ := Nat.floor_le_ceil _
  · have hqlt : (⌈β * 2 ^ k⌉₊ : ℝ) < 2 ^ k := by
      have h1 := Nat.ceil_lt_add_one (le_of_lt (mul_pos hβ0 hMpos))
      rw [div_lt_iff₀ hMpos] at hk3
      nlinarith
    exact_mod_cast hqlt
  · have hfl : (⌊α * 2 ^ k⌋₊ : ℝ) ≤ α * 2 ^ k := Nat.floor_le (le_of_lt (mul_pos hα0 hMpos))
    have ha : a = α * (π / 2) := by rw [hαdef]; field_simp
    rw [div_le_iff₀ hMpos, ha]
    calc (⌊α * 2 ^ k⌋₊ : ℝ) * (π / 2) ≤ (α * 2 ^ k) * (π / 2) :=
          mul_le_mul_of_nonneg_right hfl hL0.le
      _ = α * (π / 2) * 2 ^ k := by ring
  · have hfl := Nat.lt_floor_add_one (α * 2 ^ k)
    have ha : a = α * (π / 2) := by rw [hαdef]; field_simp
    have h2 : (π / 2) * (1 / 2 ^ k) < ε := by
      have h := mul_lt_mul_of_pos_left hk1 hL0
      rwa [mul_div_cancel₀ _ (ne_of_gt hL0)] at h
    have h4 : α < (⌊α * 2 ^ k⌋₊ : ℝ) / 2 ^ k + 1 / 2 ^ k := by
      rw [← add_div, lt_div_iff₀ hMpos]
      exact hfl
    have h3 : (⌊α * 2 ^ k⌋₊ : ℝ) * (π / 2) / 2 ^ k
        = ((⌊α * 2 ^ k⌋₊ : ℝ) / 2 ^ k) * (π / 2) := by ring
    rw [ha, h3]
    nlinarith [hL0, h2, h4]
  · have hce : β * 2 ^ k ≤ (⌈β * 2 ^ k⌉₊ : ℝ) := Nat.le_ceil _
    have hb : b = β * (π / 2) := by rw [hβdef]; field_simp
    rw [hb, le_div_iff₀ hMpos]
    calc β * (π / 2) * 2 ^ k = (β * 2 ^ k) * (π / 2) := by ring
      _ ≤ (⌈β * 2 ^ k⌉₊ : ℝ) * (π / 2) := mul_le_mul_of_nonneg_right hce hL0.le
  · have hce := Nat.ceil_lt_add_one (le_of_lt (mul_pos hβ0 hMpos))
    have hb : b = β * (π / 2) := by rw [hβdef]; field_simp
    have h2 : (π / 2) * (1 / 2 ^ k) < ε := by
      have h := mul_lt_mul_of_pos_left hk1 hL0
      rwa [mul_div_cancel₀ _ (ne_of_gt hL0)] at h
    have h4 : (⌈β * 2 ^ k⌉₊ : ℝ) / 2 ^ k < β + 1 / 2 ^ k := by
      rw [div_lt_iff₀ hMpos]
      have hone : (β + 1 / (2:ℝ) ^ k) * 2 ^ k = β * 2 ^ k + 1 := by field_simp
      rw [hone]
      exact hce
    have h3 : (⌈β * 2 ^ k⌉₊ : ℝ) * (π / 2) / 2 ^ k
        = ((⌈β * 2 ^ k⌉₊ : ℝ) / 2 ^ k) * (π / 2) := by ring
    rw [h3, hb]
    nlinarith [hL0, h2, h4]

/-- **Baek Theorem 6.4.3** for a balanced maximum cap, on any interval `[a, b] ⊂ (0, π/2)` whose
endpoints are continuity points of `arcFn K` (equivalently: `σ_K({a}) = σ_K({b}) = 0`, which holds
for all but countably many `a, b` by `countable_edgeLength_ne_zero`):

    `σ_K((a, b]) ≤ ∫_a^b k₀(g⁺_K(t)) dt`. -/
theorem sigmaK_Ioc_le_integral_balanced (hK : IsBalancedMaxCap K (π / 2))
    {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hb2 : b < π / 2)
    (hda : edgeLength K a = 0) (hdb : edgeLength K b = 0) :
    (sigmaK K (Ioc a b)).toReal ≤ ∫ t in a..b, k0 (armGp K t) := by
  obtain ⟨R', hR'⟩ := isBounded_iff_forall_norm_le.1 hK.1.isCompact.isBounded
  have hR'0 : (0:ℝ) ≤ R' := by
    obtain ⟨z, hz⟩ := hK.1.nonempty
    exact le_trans (norm_nonneg z) (hR' z hz)
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hCpos : (0:ℝ) < 2 * (1 + 2 * R') := by linarith
  obtain ⟨k, p, q, hp, hpq, hq, hA1, hA2, hB1, hB2⟩ :=
    exists_dyadic_sandwich ha0 hab hb2 (div_pos hη hCpos)
  have hmain := sigmaK_Ioc_le_integral_dyadic hK hp hpq hq hab hA1 hB1 hda hdb
  have hwiden := integral_k0_armGp_widen_le hK.1.isCompact hK.1.nonempty hR' hA1 hB1
  have hfin : (1 + 2 * R') * ((a - (p : ℝ) * (π / 2) / 2 ^ k)
      + ((q : ℝ) * (π / 2) / 2 ^ k - b)) ≤ η := by
    have h1 : (0:ℝ) < 1 + 2 * R' := by linarith
    have h2 : (a - (p : ℝ) * (π / 2) / 2 ^ k) + ((q : ℝ) * (π / 2) / 2 ^ k - b)
        ≤ 2 * (η / (2 * (1 + 2 * R'))) := by linarith
    calc (1 + 2 * R') * ((a - (p : ℝ) * (π / 2) / 2 ^ k)
            + ((q : ℝ) * (π / 2) / 2 ^ k - b))
        ≤ (1 + 2 * R') * (2 * (η / (2 * (1 + 2 * R')))) :=
          mul_le_mul_of_nonneg_left h2 h1.le
      _ = η := by field_simp
  linarith

/-- **Baek Theorem 6.4.3 at the left endpoint `0`** — the case `I = [0, b)` of Equation (6.3),
which is what Theorem 6.5.1 (`armFp_ge_of_sigmaK_le`) consumes.  Continuity points are dense
(the atoms are countable), so `σ_K((0, T]) ≤ ∫_0^T k₀(g⁺_K)` follows from the interior case by
right-continuity of `arcFn K` at `0`. -/
theorem sigmaK_Ioc_zero_le_integral (hK : IsBalancedMaxCap K (π / 2))
    {T : ℝ} (hT0 : 0 < T) (hT2 : T < π / 2) (hdT : edgeLength K T = 0) :
    (sigmaK K (Ioc 0 T)).toReal ≤ ∫ t in (0:ℝ)..T, k0 (armGp K t) := by
  have hpi := pi_pos
  have hKc := hK.1.isCompact
  have hKne := hK.1.nonempty
  obtain ⟨R', hR'⟩ := isBounded_iff_forall_norm_le.1 hKc.isBounded
  have hR'0 : (0:ℝ) ≤ R' := by
    obtain ⟨z, hz⟩ := hKne
    exact le_trans (norm_nonneg z) (hR' z hz)
  -- a sequence of continuity points decreasing to `0`
  have hdense : Dense ({t : ℝ | edgeLength K t ≠ 0}ᶜ) :=
    Set.Countable.dense_compl ℝ (countable_edgeLength_ne_zero hKc hKne)
  have hex : ∀ j : ℕ, ∃ x : ℝ, edgeLength K x = 0 ∧ x ∈ Ioo (0:ℝ) (min T (1 / (j + 1))) := by
    intro j
    have hlt : (0:ℝ) < min T (1 / ((j : ℝ) + 1)) := lt_min hT0 (by positivity)
    obtain ⟨x, hx1, hx2⟩ := hdense.exists_mem_open isOpen_Ioo (nonempty_Ioo.2 hlt)
    exact ⟨x, not_not.1 hx1, hx2⟩
  choose x hx0 hxmem using hex
  have hxpos : ∀ j, 0 < x j := fun j => (hxmem j).1
  have hxT : ∀ j, x j < T := fun j => lt_of_lt_of_le (hxmem j).2 (min_le_left _ _)
  have hx_to0 : Tendsto x atTop (𝓝 0) :=
    squeeze_zero (fun j => (hxpos j).le)
      (fun j => le_of_lt (lt_of_lt_of_le (hxmem j).2 (min_le_right _ _)))
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hx_gt : Tendsto x atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within x hx_to0
      (Eventually.of_forall hxpos)
  -- the interior case at each `x j`
  have hint : ∀ y z : ℝ, IntervalIntegrable (fun t => k0 (armGp K t)) volume y z :=
    fun y z => intervalIntegrable_k0_comp (intervalIntegrable_armGp hKc hKne _ _)
  have hstep : ∀ j, (sigmaK K (Ioc (x j) T)).toReal
      ≤ (∫ t in (0:ℝ)..T, k0 (armGp K t)) + (1 + 2 * R') * x j := by
    intro j
    have h1 := sigmaK_Ioc_le_integral_balanced hK (hxpos j) (hxT j).le hT2 (hx0 j) hdT
    have h2 : (∫ t in (0:ℝ)..(x j), k0 (armGp K t)) + ∫ t in (x j)..T, k0 (armGp K t)
        = ∫ t in (0:ℝ)..T, k0 (armGp K t) :=
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
    have h3 : (0:ℝ) ≤ ∫ t in (0:ℝ)..(x j), k0 (armGp K t) :=
      intervalIntegral.integral_nonneg (μ := volume) (hxpos j).le fun t _ => k0_nonneg _
    have h4 : (∫ t in (0:ℝ)..(x j), k0 (armGp K t)) ≤ (1 + 2 * R') * x j := by
      have hbd : ∀ t : ℝ, k0 (armGp K t) ≤ 1 + 2 * R' :=
        fun t => (k0_le_one_add_abs _).trans (by linarith [abs_armGp_le hKc hKne hR' t])
      have h := intervalIntegral.integral_mono_on (hxpos j).le (hint 0 (x j))
        (intervalIntegrable_const (μ := volume) (c := 1 + 2 * R')) fun t _ => hbd t
      rw [intervalIntegral.integral_const, smul_eq_mul] at h
      calc (∫ t in (0:ℝ)..(x j), k0 (armGp K t)) ≤ (x j - 0) * (1 + 2 * R') := h
        _ = (1 + 2 * R') * x j := by ring
    linarith
  -- pass to the limit
  have hL : Tendsto (fun j => (sigmaK K (Ioc (x j) T)).toReal) atTop
      (𝓝 (arcFn K T - arcFn K 0)) := by
    have harc := (tendsto_arcFn_nhdsGT hKc hKne 0).comp hx_gt
    have hconst : Tendsto (fun _ : ℕ => arcFn K T) atTop (𝓝 (arcFn K T)) := tendsto_const_nhds
    refine (hconst.sub harc).congr fun j => ?_
    exact (sigmaK_Ioc_toReal hKc hKne (hxT j).le).symm
  have hR : Tendsto (fun j => (∫ t in (0:ℝ)..T, k0 (armGp K t)) + (1 + 2 * R') * x j) atTop
      (𝓝 ((∫ t in (0:ℝ)..T, k0 (armGp K t)) + (1 + 2 * R') * 0)) :=
    tendsto_const_nhds.add (hx_to0.const_mul _)
  rw [mul_zero, add_zero] at hR
  have hgoal := le_of_tendsto_of_tendsto' hL hR hstep
  rw [sigmaK_Ioc_toReal hKc hKne hT0.le]
  exact hgoal

/-- **`σ_K` has no atoms in `(0, π/2)`** for a balanced maximum cap — Baek's Corollary 6.4.4
without the Radon–Nikodym theorem.  Squeeze `{t}` between two continuity points `a < t < b` with
`b − a < 2ε`: Theorem 6.4.3 gives `σ_K({t}) ≤ σ_K((a,b]) ≤ ∫_a^b k₀(g⁺_K) ≤ (1+2R)(b−a)`. -/
theorem edgeLength_eq_zero_of_balanced (hK : IsBalancedMaxCap K (π / 2)) {t : ℝ}
    (ht0 : 0 < t) (ht2 : t < π / 2) : edgeLength K t = 0 := by
  have hKc := hK.1.isCompact
  have hKne := hK.1.nonempty
  obtain ⟨R', hR'⟩ := isBounded_iff_forall_norm_le.1 hKc.isBounded
  have hR'0 : (0:ℝ) ≤ R' := by
    obtain ⟨z, hz⟩ := hKne
    exact le_trans (norm_nonneg z) (hR' z hz)
  have hdense : Dense ({s : ℝ | edgeLength K s ≠ 0}ᶜ) :=
    Set.Countable.dense_compl ℝ (countable_edgeLength_ne_zero hKc hKne)
  refine le_antisymm (le_of_forall_pos_le_add fun η hη => ?_) (edgeLength_nonneg hKc hKne t)
  have hC : (0:ℝ) < 2 * (1 + 2 * R') := by linarith
  set ε : ℝ := η / (2 * (1 + 2 * R')) with hεdef
  have hε : 0 < ε := div_pos hη hC
  obtain ⟨a, ha0, hamem⟩ : ∃ a, edgeLength K a = 0 ∧ a ∈ Ioo (max 0 (t - ε)) t := by
    have hlt : max 0 (t - ε) < t := max_lt ht0 (by linarith)
    obtain ⟨y, hy1, hy2⟩ := hdense.exists_mem_open (U := Ioo (max 0 (t - ε)) t) isOpen_Ioo
      (nonempty_Ioo.2 hlt)
    exact ⟨y, not_not.1 hy1, hy2⟩
  obtain ⟨b, hb0, hbmem⟩ : ∃ b, edgeLength K b = 0 ∧ b ∈ Ioo t (min (π / 2) (t + ε)) := by
    have hlt : t < min (π / 2) (t + ε) := lt_min ht2 (by linarith)
    obtain ⟨y, hy1, hy2⟩ := hdense.exists_mem_open (U := Ioo t (min (π / 2) (t + ε))) isOpen_Ioo
      (nonempty_Ioo.2 hlt)
    exact ⟨y, not_not.1 hy1, hy2⟩
  have hapos : 0 < a := lt_of_le_of_lt (le_max_left 0 (t - ε)) hamem.1
  have hblt : b < π / 2 := lt_of_lt_of_le hbmem.2 (min_le_left _ _)
  have hab : a ≤ b := le_of_lt (lt_trans hamem.2 hbmem.1)
  have hmain := sigmaK_Ioc_le_integral_balanced hK hapos hab hblt ha0 hb0
  have hmono : sigmaK K {t} ≤ sigmaK K (Ioc a b) := by
    refine measure_mono ?_
    intro s hs
    rw [mem_singleton_iff] at hs
    subst hs
    exact ⟨hamem.2, hbmem.1.le⟩
  have hdiff : 0 ≤ arcFn K b - arcFn K a := by linarith [arcFn_mono hKc hKne hab]
  rw [sigmaK_singleton hKc hKne, sigmaK_Ioc hKc hKne] at hmono
  have hle : edgeLength K t ≤ arcFn K b - arcFn K a :=
    (ENNReal.ofReal_le_ofReal_iff hdiff).1 hmono
  rw [← sigmaK_Ioc_toReal hKc hKne hab] at hle
  -- bound the integral
  have hbd : ∀ r : ℝ, k0 (armGp K r) ≤ 1 + 2 * R' :=
    fun r => (k0_le_one_add_abs _).trans (by linarith [abs_armGp_le hKc hKne hR' r])
  have hint : IntervalIntegrable (fun r => k0 (armGp K r)) volume a b :=
    intervalIntegrable_k0_comp (intervalIntegrable_armGp hKc hKne a b)
  have hI := intervalIntegral.integral_mono_on hab hint
    (intervalIntegrable_const (μ := volume) (c := 1 + 2 * R')) fun r _ => hbd r
  rw [intervalIntegral.integral_const, smul_eq_mul] at hI
  have hba : b - a < 2 * ε := by
    have h1 : t - ε < a := lt_of_le_of_lt (le_max_right 0 (t - ε)) hamem.1
    have h2 : b < t + ε := lt_of_lt_of_le hbmem.2 (min_le_right _ _)
    linarith
  have hfin : (b - a) * (1 + 2 * R') ≤ η := by
    have h1 : (0:ℝ) < 1 + 2 * R' := by linarith
    have h2 : (b - a) * (1 + 2 * R') ≤ (2 * ε) * (1 + 2 * R') :=
      mul_le_mul_of_nonneg_right hba.le h1.le
    have h3 : (2 * ε) * (1 + 2 * R') = η := by rw [hεdef]; field_simp
    linarith
  linarith

/-- Theorem 6.4.3 with no continuity hypothesis. -/
theorem sigmaK_Ioc_le_integral_balanced' (hK : IsBalancedMaxCap K (π / 2))
    {a b : ℝ} (ha0 : 0 < a) (hab : a ≤ b) (hb2 : b < π / 2) :
    (sigmaK K (Ioc a b)).toReal ≤ ∫ t in a..b, k0 (armGp K t) :=
  sigmaK_Ioc_le_integral_balanced hK ha0 hab hb2
    (edgeLength_eq_zero_of_balanced hK ha0 (lt_of_le_of_lt hab hb2))
    (edgeLength_eq_zero_of_balanced hK (lt_of_lt_of_le ha0 hab) hb2)

/-- Theorem 6.4.3 on `(0, T]` with no continuity hypothesis. -/
theorem sigmaK_Ioc_zero_le_integral' (hK : IsBalancedMaxCap K (π / 2))
    {T : ℝ} (hT0 : 0 < T) (hT2 : T < π / 2) :
    (sigmaK K (Ioc 0 T)).toReal ≤ ∫ t in (0:ℝ)..T, k0 (armGp K t) :=
  sigmaK_Ioc_zero_le_integral hK hT0 hT2 (edgeLength_eq_zero_of_balanced hK hT0 hT2)

/-- **Baek Theorem 6.5.1** for a balanced maximum cap: combining Theorem 6.4.3 with the identity
form of Theorem 6.2.5 (`armFp_ge_of_sigmaK_le`, `Sofa/ArmBound.lean`),

    `f⁺_K(0) + ∫_0^T m₀(g⁺_K(s)) ds ≤ f⁺_K(T)`

for every `T ∈ (0, π/2)`. -/
theorem armFp_ge_balanced (hK : IsBalancedMaxCap K (π / 2)) {T : ℝ}
    (hT0 : 0 < T) (hT2 : T < π / 2) :
    armFp K 0 + ∫ s in (0:ℝ)..T, m0 (armGp K s) ≤ armFp K T :=
  armFp_ge_of_sigmaK_le hK.1.isCompact hK.1.nonempty
    (intervalIntegrable_armGp hK.1.isCompact hK.1.nonempty 0 T)
    (intervalIntegrable_k0_comp (intervalIntegrable_armGp hK.1.isCompact hK.1.nonempty 0 T))
    (sigmaK_Ioc_zero_le_integral' hK hT0 hT2) hT0.le

end Balanced

end Sofa
