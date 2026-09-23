/-
# Sofa/Minkowski.lean — Baek §7.1 for planar convex bodies (Thm 7.1.1–7.1.3)

The barycentric operation on convex bodies is `c_λ(K₁,K₂) = (1−λ)K₁ + λK₂` (Minkowski).  The
embedding of Def 7.1.1 is `K ↦ h_K`, so *everything* reduces to

    `h_{c_λ(K₁,K₂)} = (1−λ) h_{K₁} + λ h_{K₂}`   (`supportFn_mix`)

together with the fact that each object of Chapters 2 and 5 is an explicit expression in `h`:

* `v_K(a,b)` is *literally linear* in `(h_K(a), h_K(b))` (Def 2.1.14), and `v⁺_K(t)` is its limit
  as `b → t⁺` (Thm 2.1.3) — so `v⁺_K` is convex-linear (Thm 7.1.2 (2));
* `arcFn K t = ⟪v⁺_K(t), v_t⟫ + ∫_0^t h_K` is then convex-linear, so `σ_K` is too (Thm 7.1.2 (3));
* `|K| = ½∫ h_K dσ_K` (Thm 7.1.3) is therefore a quadratic functional.

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.Quadratic
import Sofa.Translate

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped Pointwise EuclideanGeometry RealInnerProductSpace

namespace Sofa

/-! ## The barycentric operation -/

/-- `c_λ(A, B) = (1−λ)A + λB` (Minkowski). -/
def mix (l : ℝ) (A B : Set ℝ²) : Set ℝ² := (1 - l) • A + l • B

lemma mem_mix {l : ℝ} {A B : Set ℝ²} {q : ℝ²} :
    q ∈ mix l A B ↔ ∃ a ∈ A, ∃ b ∈ B, (1 - l) • a + l • b = q := by
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨(1 - l) • a, ⟨a, ha, rfl⟩, l • b, ⟨b, hb, rfl⟩, rfl⟩

lemma isCompact_mix {l : ℝ} {A B : Set ℝ²} (hA : IsCompact A) (hB : IsCompact B) :
    IsCompact (mix l A B) := by
  have h1 : IsCompact ((1 - l) • A) := by
    rw [← Set.image_smul]; exact hA.image (continuous_const_smul _)
  have h2 : IsCompact (l • B) := by
    rw [← Set.image_smul]; exact hB.image (continuous_const_smul _)
  exact h1.add h2

lemma nonempty_mix {l : ℝ} {A B : Set ℝ²} (hA : A.Nonempty) (hB : B.Nonempty) :
    (mix l A B).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact ⟨_, mem_mix.2 ⟨a, ha, b, hb, rfl⟩⟩

lemma convex_mix {l : ℝ} {A B : Set ℝ²} (hA : Convex ℝ A) (hB : Convex ℝ B) :
    Convex ℝ (mix l A B) := (hA.smul _).add (hB.smul _)

/-! ## Theorem 7.1.1 / 7.1.2 (1): the support function -/

theorem supportFn_mix {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (t : ℝ) :
    supportFn (mix l A B) t = (1 - l) * supportFn A t + l * supportFn B t := by
  have hM := isCompact_mix (l := l) hA hB
  have hMne := nonempty_mix (l := l) hAne hBne
  refine le_antisymm ?_ ?_
  · rw [supportFn_le_iff hM hMne]
    intro q hq
    obtain ⟨a, ha, b, hb, hab⟩ := mem_mix.1 hq
    have h1 := le_supportFn hA ha t
    have h2 := le_supportFn hB hb t
    have hpe : ⟪q, u t⟫ = (1 - l) * ⟪a, u t⟫ + l * ⟪b, u t⟫ := by
      rw [← hab, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rw [hpe]
    nlinarith
  · obtain ⟨a, ha, hae⟩ := exists_supportFn_eq hA hAne t
    obtain ⟨b, hb, hbe⟩ := exists_supportFn_eq hB hBne t
    have h := le_supportFn hM (mem_mix.2 ⟨a, ha, b, hb, rfl⟩) t
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hae, hbe] at h
    exact h

/-! ## Theorem 7.1.2 (2): the vertices -/

lemma vtx2_mix {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (a b : ℝ) :
    vtx2 (mix l A B) a b = (1 - l) • vtx2 A a b + l • vtx2 B a b := by
  rw [vtx2, vtx2, vtx2, supportFn_mix hA hAne hB hBne hl0 hl1 a,
    supportFn_mix hA hAne hB hBne hl0 hl1 b]
  rw [show ((1 - l) * supportFn A b + l * supportFn B b
        - ((1 - l) * supportFn A a + l * supportFn B a) * cos (b - a)) / sin (b - a)
      = (1 - l) * ((supportFn A b - supportFn A a * cos (b - a)) / sin (b - a))
        + l * ((supportFn B b - supportFn B a * cos (b - a)) / sin (b - a)) from by
      field_simp; ring]
  module

/-- **Theorem 7.1.2 (2).** The vertex `v⁺_K(t)` is convex-linear in `K`. -/
theorem vtxP_mix {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (t : ℝ) :
    vtxP (mix l A B) t = (1 - l) • vtxP A t + l • vtxP B t := by
  have hM := isCompact_mix (l := l) hA hB
  have hMne := nonempty_mix (l := l) hAne hBne
  have h1 : Tendsto (vtx2 (mix l A B) t) (𝓝[>] t) (𝓝 (vtxP (mix l A B) t)) :=
    tendsto_vtx2_right hM hMne t
  have h2 : Tendsto (vtx2 (mix l A B) t) (𝓝[>] t)
      (𝓝 ((1 - l) • vtxP A t + l • vtxP B t)) := by
    have hA' := (tendsto_vtx2_right hA hAne t).const_smul (1 - l)
    have hB' := (tendsto_vtx2_right hB hBne t).const_smul l
    have := hA'.add hB'
    refine this.congr fun s => ?_
    exact (vtx2_mix hA hAne hB hBne hl0 hl1 t s).symm
  exact tendsto_nhds_unique h1 h2

/-- `m⁺_K(t) = ⟪v⁺_K(t), v_t⟫` is convex-linear too. -/
theorem edgeMax_mix {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (t : ℝ) :
    edgeMax (mix l A B) t = (1 - l) * edgeMax A t + l * edgeMax B t := by
  rw [← inner_vtxP_v, ← inner_vtxP_v, ← inner_vtxP_v, vtxP_mix hA hAne hB hBne hl0 hl1 t,
    inner_add_left, real_inner_smul_left, real_inner_smul_left]

/-! ## Theorem 7.1.2 (3): the surface area measure -/

theorem arcFn_mix {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (t : ℝ) :
    arcFn (mix l A B) t = (1 - l) * arcFn A t + l * arcFn B t := by
  have hI : ∫ s in (0:ℝ)..t, supportFn (mix l A B) s
      = (1 - l) * (∫ s in (0:ℝ)..t, supportFn A s) + l * (∫ s in (0:ℝ)..t, supportFn B s) := by
    have hpt : ∀ s : ℝ, supportFn (mix l A B) s = (1 - l) * supportFn A s + l * supportFn B s :=
      fun s => supportFn_mix hA hAne hB hBne hl0 hl1 s
    simp only [hpt]
    rw [intervalIntegral.integral_add ((integrable_supportFn hA hAne 0 t).const_mul _)
      ((integrable_supportFn hB hBne 0 t).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [arcFn, arcFn, arcFn, inner_vtxP_v, inner_vtxP_v, inner_vtxP_v,
    edgeMax_mix hA hAne hB hBne hl0 hl1 t, hI]
  ring

/-- **Theorem 7.1.2 (3).** The surface area measure is convex-linear in `K`. -/
theorem sigmaK_mix {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    sigmaK (mix l A B)
      = ENNReal.ofReal (1 - l) • sigmaK A + ENNReal.ofReal l • sigmaK B := by
  have hM := isCompact_mix (l := l) hA hB
  have hMne := nonempty_mix (l := l) hAne hBne
  refine Measure.ext_of_Ioc _ _ fun a b hab => ?_
  have hmA : 0 ≤ arcFn A b - arcFn A a := by linarith [arcFn_mono hA hAne hab.le]
  have hmB : 0 ≤ arcFn B b - arcFn B a := by linarith [arcFn_mono hB hBne hab.le]
  rw [sigmaK_Ioc hM hMne, arcFn_mix hA hAne hB hBne hl0 hl1 b,
    arcFn_mix hA hAne hB hBne hl0 hl1 a]
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, sigmaK_Ioc hA hAne,
    sigmaK_Ioc hB hBne, smul_eq_mul, smul_eq_mul,
    ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hl0,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-! ## The convex domain of bodies, and `|K|` as a quadratic functional (Thm 7.1.1, 7.1.3) -/

/-- **Theorem 7.1.1.** A family of nonempty planar bodies closed under `c_λ` is a convex domain. -/
def bodyDomain (S : Set (Set ℝ²)) (hne : ∀ A ∈ S, A.Nonempty)
    (hclosed : ∀ A ∈ S, ∀ B ∈ S, ∀ l : ℝ, 0 ≤ l → l ≤ 1 → mix l A B ∈ S) :
    ConvexDomain (Set ℝ²) where
  carrier := S
  bary := mix
  mem := by intro x hx y hy l hl0 hl1; exact hclosed x hx y hy l hl0 hl1
  bary_zero := by
    intro x _ y hy
    rw [mix, sub_zero, one_smul, Set.zero_smul_set (hne y hy), add_zero]
  bary_one := by
    intro x hx y _
    rw [mix, sub_self, Set.zero_smul_set (hne x hx), one_smul, zero_add]

/-- The convex-bilinear form behind `|K| = ½ ∫ h_K dσ_K`. -/
def areaB (t₀ : ℝ) (A B : Set ℝ²) : ℝ :=
  (∫ t in Ioc t₀ (t₀ + 2 * π), supportFn A t ∂(sigmaK B)) / 2

lemma areaB_self (K : Set ℝ²) (t₀ : ℝ) : areaB t₀ K K = curveG K t₀ (t₀ + 2 * π) := rfl

/-- Integrability of one body's support function against another body's surface measure. -/
lemma integrableOn_supportFn_sigmaK' {A : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty)
    (B : Set ℝ²) (a b : ℝ) : IntegrableOn (supportFn A) (Ioc a b) (sigmaK B) :=
  (ContinuousOn.integrableOn_compact isCompact_Icc
    ((continuous_supportFn hA hAne).continuousOn)).mono_set Ioc_subset_Icc_self

/-- `areaB` is convex-linear in its first (support-function) slot. -/
theorem areaB_mix_left {A A' B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty)
    (hA' : IsCompact A') (hA'ne : A'.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (t₀ : ℝ) :
    areaB t₀ (mix l A A') B = (1 - l) * areaB t₀ A B + l * areaB t₀ A' B := by
  have hpt : ∀ s : ℝ, supportFn (mix l A A') s = (1 - l) * supportFn A s + l * supportFn A' s :=
    fun s => supportFn_mix hA hAne hA' hA'ne hl0 hl1 s
  rw [areaB, areaB, areaB]
  simp only [hpt]
  rw [integral_add ((integrableOn_supportFn_sigmaK' hA hAne B t₀ (t₀ + 2 * π)).const_mul _)
    ((integrableOn_supportFn_sigmaK' hA' hA'ne B t₀ (t₀ + 2 * π)).const_mul _),
    integral_const_mul, integral_const_mul]
  ring

/-- `areaB` is convex-linear in its second (measure) slot. -/
theorem areaB_mix_right {A B B' : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty)
    (hB : IsCompact B) (hBne : B.Nonempty) (hB' : IsCompact B') (hB'ne : B'.Nonempty)
    {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (t₀ : ℝ) :
    areaB t₀ A (mix l B B') = (1 - l) * areaB t₀ A B + l * areaB t₀ A B' := by
  have hint1 := integrableOn_supportFn_sigmaK' hA hAne B t₀ (t₀ + 2 * π)
  have hint2 := integrableOn_supportFn_sigmaK' hA hAne B' t₀ (t₀ + 2 * π)
  have hs1 : ENNReal.ofReal (1 - l) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hs2 : ENNReal.ofReal l ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [areaB, areaB, areaB, sigmaK_mix hB hBne hB' hB'ne hl0 hl1]
  rw [Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
    integral_add_measure (hint1.smul_measure hs1) (hint2.smul_measure hs2),
    integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hl0]
  simp only [smul_eq_mul]
  ring

/-- **Theorem 7.1.3 as a convex-domain statement**: the area is a quadratic functional. -/
theorem isQuadraticOn_volumeReal (S : Set (Set ℝ²)) (hne : ∀ A ∈ S, A.Nonempty)
    (hclosed : ∀ A ∈ S, ∀ B ∈ S, ∀ l : ℝ, 0 ≤ l → l ≤ 1 → mix l A B ∈ S)
    (hcpt : ∀ A ∈ S, IsCompact A) (hcvx : ∀ A ∈ S, Convex ℝ A)
    (hint : ∀ A ∈ S, (interior A).Nonempty) (t₀ : ℝ) :
    IsQuadraticOn (bodyDomain S hne hclosed) (fun K => volume.real K) := by
  refine ⟨areaB t₀, ⟨fun A hA => ?_, fun B hB => ?_⟩, fun K hK => ?_⟩
  · intro x hx y hy l hl0 hl1
    exact areaB_mix_right (hcpt A hA) (hne A hA) (hcpt x hx) (hne x hx) (hcpt y hy) (hne y hy)
      hl0 hl1 t₀
  · intro x hx y hy l hl0 hl1
    exact areaB_mix_left (hcpt x hx) (hne x hx) (hcpt y hy) (hne y hy) hl0 hl1 t₀
  · rw [areaB_self]
    exact volumeReal_eq_curveG_of_interior_nonempty (hcpt K hK) (hcvx K hK) (hint K hK) t₀
