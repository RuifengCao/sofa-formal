/-
# Sofa/Triangle.lean — the area of a plane triangle

`|conv{0, A, B}| = ½ |A × B|`, where `A × B = A₀B₁ − A₁B₀`.

This is the atom of the planned proof of Baek Thm 7.1.3 (`|K| = ½ ∫ h_K dσ_K`), whose printed
proof goes through Green's theorem for a rectifiable Jordan curve (not available in Mathlib) —
see `blueprint/ch3-8.md` §15.3.

Proof: the triangle is the image of the standard triangle `T₀ = {(x,y) : 0 ≤ x, 0 ≤ y, x+y ≤ 1}`
under the linear map `(x,y) ↦ x A + y B`, whose determinant is `A × B`; `|T₀| = 1/2` is a
one-dimensional Cavalieri computation (`Sofa/Graph.lean`).

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.Graph

noncomputable section

open Real Set Filter Topology MeasureTheory MovingSofa
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

/-! ## The cross product -/

/-- The scalar cross product `A × B = A₀B₁ − A₁B₀`. -/
def cross (p q : ℝ²) : ℝ := p 0 * q 1 - p 1 * q 0

lemma cross_self (p : ℝ²) : cross p p = 0 := by rw [cross]; ring

lemma cross_comm (p q : ℝ²) : cross p q = -cross q p := by rw [cross, cross]; ring

lemma cross_add_right (p q r : ℝ²) : cross p (q + r) = cross p q + cross p r := by
  simp only [cross, PiLp.add_apply]; ring

lemma cross_smul_right (c : ℝ) (p q : ℝ²) : cross p (c • q) = c * cross p q := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring

lemma cross_add_left (p q r : ℝ²) : cross (p + q) r = cross p r + cross q r := by
  simp only [cross, PiLp.add_apply]; ring

lemma cross_smul_left (c : ℝ) (p q : ℝ²) : cross (c • p) q = c * cross p q := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring

/-- **Cramer's rule in the plane**: `(A × C) B = (B × C) A + (A × B) C`. -/
lemma cross_cramer (A B C : ℝ²) :
    cross A C • B = cross B C • A + cross A B • C := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- The scalar form of Cramer's rule used for wedge comparisons. -/
lemma cross_cramer_mul (A B C q : ℝ²) :
    cross A C * cross B q = cross B C * cross A q + cross A B * cross C q := by
  have h := congrArg (fun x => cross x q) (cross_cramer A B C)
  simpa only [cross_smul_left, cross_add_left] using h

/-- `p × u_t = −⟪p, v_t⟫`. -/
lemma cross_u (p : ℝ²) (t : ℝ) : cross p (u t) = -⟪p, v t⟫ := by
  simp only [cross, inner_eq, u_coord_zero, u_coord_one, v_coord_zero, v_coord_one]; ring

/-- `p × v_t = ⟪p, u_t⟫`. -/
lemma cross_v (p : ℝ²) (t : ℝ) : cross p (v t) = ⟪p, u t⟫ := by
  simp only [cross, inner_eq, u_coord_zero, u_coord_one, v_coord_zero, v_coord_one]; ring

/-! ## The standard triangle -/

/-- The lower boundary of the standard triangle (`1` outside `[0,1]`, to make the slice empty). -/
def loT : ℝ → ℝ := (Icc (0:ℝ) 1).piecewise (fun _ => 0) (fun _ => 1)

/-- The upper boundary of the standard triangle. -/
def hiT : ℝ → ℝ := (Icc (0:ℝ) 1).piecewise (fun x => 1 - x) (fun _ => 0)

lemma measurable_loT : Measurable loT :=
  Measurable.piecewise measurableSet_Icc measurable_const measurable_const

lemma measurable_hiT : Measurable hiT :=
  Measurable.piecewise measurableSet_Icc (by fun_prop) measurable_const

/-- The standard triangle `{(x, y) : 0 ≤ x, 0 ≤ y, x + y ≤ 1}`. -/
def stdTri : Set ℝ² := {p : ℝ² | loT (p 0) ≤ p 1 ∧ p 1 ≤ hiT (p 0)}

lemma mem_stdTri {p : ℝ²} : p ∈ stdTri ↔ 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 0 + p 1 ≤ 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hx : p 0 ∈ Icc (0:ℝ) 1
    · rw [loT, Set.piecewise_eq_of_mem _ _ _ hx] at h1
      rw [hiT, Set.piecewise_eq_of_mem _ _ _ hx] at h2
      exact ⟨hx.1, h1, by linarith⟩
    · rw [loT, Set.piecewise_eq_of_notMem _ _ _ hx] at h1
      rw [hiT, Set.piecewise_eq_of_notMem _ _ _ hx] at h2
      linarith
  · rintro ⟨h0, h1, h2⟩
    have hx : p 0 ∈ Icc (0:ℝ) 1 := ⟨h0, by linarith⟩
    rw [stdTri, Set.mem_ofPred_eq, loT, hiT, Set.piecewise_eq_of_mem _ _ _ hx,
      Set.piecewise_eq_of_mem _ _ _ hx]
    exact ⟨h1, by linarith⟩

theorem volume_stdTri : volume stdTri = ENNReal.ofReal (1 / 2) := by
  rw [stdTri, volume_between_Icc measurable_loT measurable_hiT]
  have hcongr : ∀ x : ℝ, ENNReal.ofReal (hiT x - loT x)
      = (Icc (0:ℝ) 1).indicator (fun x => ENNReal.ofReal (1 - x)) x := by
    intro x
    by_cases hx : x ∈ Icc (0:ℝ) 1
    · rw [Set.indicator_of_mem hx, loT, hiT, Set.piecewise_eq_of_mem _ _ _ hx,
        Set.piecewise_eq_of_mem _ _ _ hx, sub_zero]
    · rw [Set.indicator_of_notMem hx, loT, hiT, Set.piecewise_eq_of_notMem _ _ _ hx,
        Set.piecewise_eq_of_notMem _ _ _ hx]
      simp
  rw [lintegral_congr hcongr, lintegral_indicator measurableSet_Icc]
  have hint : IntegrableOn (fun x : ℝ => 1 - x) (Icc 0 1) volume :=
    (continuous_const.sub continuous_id).integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Icc (0:ℝ) 1)] fun x : ℝ => 1 - x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    simp only [Pi.zero_apply]
    linarith [hx.2]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    intervalIntegral.intervalIntegrable_id]
  rw [intervalIntegral.integral_const, integral_id]
  norm_num

/-! ## The linear map and its determinant -/

/-- `(x, y) ↦ x A + y B`. -/
def triLin (A B : ℝ²) : ℝ² →ₗ[ℝ] ℝ² where
  toFun p := p 0 • A + p 1 • B
  map_add' p q := by simp only [PiLp.add_apply, add_smul]; abel
  map_smul' c p := by
    simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]

@[simp] lemma triLin_apply (A B : ℝ²) (p : ℝ²) : triLin A B p = p 0 • A + p 1 • B := rfl

lemma det_triLin (A B : ℝ²) : LinearMap.det (triLin A B) = cross A B := by
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin 2) ℝ ℝ², b = (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    := ⟨_, rfl⟩
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  have hb0 : b 0 = e₀ := by rw [hb]; ext i; fin_cases i <;> simp [e₀, EuclideanSpace.single]
  have hb1 : b 1 = e₁ := by rw [hb]; ext i; fin_cases i <;> simp [e₁, EuclideanSpace.single]
  have hrep : ∀ (x : ℝ²) (i : Fin 2), b.repr x i = x i := by
    intro x i; rw [hb]; simp
  simp only [LinearMap.toMatrix_apply, hb0, hb1, hrep, triLin_apply, cross]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, e₀, e₁]
  norm_num
  ring

/-! ## The triangle and its area -/

/-- The triangle with vertices `0`, `A`, `B`. -/
def tri (A B : ℝ²) : Set ℝ² := triLin A B '' stdTri

lemma mem_tri {A B p : ℝ²} :
    p ∈ tri A B ↔ ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1 ∧ p = s • A + t • B := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨h0, h1, h2⟩ := mem_stdTri.1 hq
    exact ⟨q 0, q 1, h0, h1, h2, rfl⟩
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    exact ⟨pt s t, mem_stdTri.2 (by simpa using ⟨hs, ht, hst⟩), by simp⟩

/-- **The area of a triangle**: `|conv{0, A, B}| = ½ |A × B|`. -/
theorem volume_tri (A B : ℝ²) : volume (tri A B) = ENNReal.ofReal (|cross A B| / 2) := by
  rw [tri, Measure.addHaar_image_linearMap, det_triLin, volume_stdTri,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

theorem measureReal_tri (A B : ℝ²) : volume.real (tri A B) = |cross A B| / 2 := by
  rw [measureReal_def, volume_tri, ENNReal.toReal_ofReal (by positivity)]

/-! ## Triangles with a general apex, and containment in a convex set -/

/-- The triangle with vertices `P`, `Q`, `R`. -/
def triAt (P Q R : ℝ²) : Set ℝ² := (fun x => x + P) '' tri (Q - P) (R - P)

theorem volume_triAt (P Q R : ℝ²) :
    volume (triAt P Q R) = ENNReal.ofReal (|cross (Q - P) (R - P)| / 2) := by
  have h : triAt P Q R = tr P (tri (Q - P) (R - P)) := rfl
  rw [h, volume_tr, volume_tri]

theorem measureReal_triAt (P Q R : ℝ²) :
    volume.real (triAt P Q R) = |cross (Q - P) (R - P)| / 2 := by
  rw [measureReal_def, volume_triAt, ENNReal.toReal_ofReal (by positivity)]

/-- A triangle with vertices in a convex set stays inside it. -/
theorem tri_subset_of_convex {S : Set ℝ²} (hS : Convex ℝ S) {A B : ℝ²} (h0 : (0:ℝ²) ∈ S)
    (hA : A ∈ S) (hB : B ∈ S) : tri A B ⊆ S := by
  rintro p hp
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := mem_tri.1 hp
  rcases eq_or_lt_of_le (by linarith : (0:ℝ) ≤ s + t) with h | h
  · have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    simpa [hs0, ht0] using h0
  · have hne : s + t ≠ 0 := ne_of_gt h
    have hw : (s / (s + t)) • A + (t / (s + t)) • B ∈ S :=
      hS hA hB (by positivity) (by positivity) (by field_simp)
    have heq : (s + t) • ((s / (s + t)) • A + (t / (s + t)) • B) + (1 - (s + t)) • (0 : ℝ²)
        = s • A + t • B := by
      have e1 : (s + t) * (s / (s + t)) = s := by field_simp
      have e2 : (s + t) * (t / (s + t)) = t := by field_simp
      rw [smul_add, smul_zero, add_zero, smul_smul, smul_smul, e1, e2]
    rw [← heq]
    exact hS hw h0 (le_of_lt h) (by linarith) (by ring)

/-- Points of `tri A B` lie in the wedge between the rays `ℝ≥0 A` and `ℝ≥0 B`. -/
lemma cross_nonneg_of_mem_tri {A B p : ℝ²} (hAB : 0 ≤ cross A B) (hp : p ∈ tri A B) :
    0 ≤ cross A p ∧ cross B p ≤ 0 := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := mem_tri.1 hp
  have e1 : cross A (s • A + t • B) = t * cross A B := by
    rw [cross_add_right, cross_smul_right, cross_smul_right, cross_self, mul_zero, zero_add]
  have e2 : cross B (s • A + t • B) = -(s * cross A B) := by
    rw [cross_add_right, cross_smul_right, cross_smul_right, cross_self, mul_zero, add_zero,
      cross_comm B A]
    ring
  rw [e1, e2]
  exact ⟨mul_nonneg ht hAB, by nlinarith⟩

/-! ## Wedges -/

/-- The closed wedge between the rays `ℝ≥0 A` and `ℝ≥0 B` (counterclockwise from `A` to `B`). -/
def wedgeC (A B : ℝ²) : Set ℝ² := {q | 0 ≤ cross A q ∧ cross B q ≤ 0}

lemma tri_subset_wedgeC {A B : ℝ²} (hAB : 0 ≤ cross A B) : tri A B ⊆ wedgeC A B :=
  fun _ hp => cross_nonneg_of_mem_tri hAB hp

/-- Enlarging the wedge counterclockwise: `wedge(A,B) ⊆ wedge(A,C)`. -/
lemma wedgeC_subset_left {A B C : ℝ²} (hAB : 0 < cross A B) (hBC : 0 ≤ cross B C)
    (hAC : 0 < cross A C) : wedgeC A B ⊆ wedgeC A C := by
  rintro q ⟨h1, h2⟩
  refine ⟨h1, ?_⟩
  have h := cross_cramer_mul A B C q
  nlinarith

/-- Enlarging the wedge clockwise: `wedge(B,C) ⊆ wedge(A,C)`. -/
lemma wedgeC_subset_right {A B C : ℝ²} (hAB : 0 ≤ cross A B) (hBC : 0 < cross B C)
    (hAC : 0 < cross A C) : wedgeC B C ⊆ wedgeC A C := by
  rintro q ⟨h1, h2⟩
  refine ⟨?_, h2⟩
  have h := cross_cramer_mul A B C q
  nlinarith

/-- The two sub-wedges cover the big one (a trivial dichotomy). -/
lemma wedgeC_subset_union (A B C : ℝ²) : wedgeC A C ⊆ wedgeC A B ∪ wedgeC B C := by
  rintro q ⟨h1, h2⟩
  rcases le_or_gt (cross B q) 0 with h | h
  · exact Or.inl ⟨h1, h⟩
  · exact Or.inr ⟨h.le, h2⟩

/-- The two sub-wedges overlap only in the line `ℝ B`. -/
lemma wedgeC_inter_subset (A B C : ℝ²) :
    wedgeC A B ∩ wedgeC B C ⊆ {q | cross B q = 0} := by
  rintro q ⟨⟨-, h1⟩, ⟨h2, -⟩⟩
  exact le_antisymm h1 h2

/-- A degenerate wedge (`B` on the ray `ℝ>0 A`) is contained in a line. -/
lemma wedgeC_subset_line {A B : ℝ²} {μ : ℝ} (hμ : 0 < μ) (hB : B = μ • A) :
    wedgeC A B ⊆ {q | cross A q = 0} := by
  rintro q ⟨h1, h2⟩
  rw [hB, cross_smul_left] at h2
  exact le_antisymm (by nlinarith) h1

/-- Two vectors with vanishing cross product are proportional. -/
lemma exists_smul_of_cross_eq_zero {A B : ℝ²} (hA : A ≠ 0) (h : cross A B = 0) :
    ∃ μ : ℝ, B = μ • A := by
  have hco : A 0 * B 1 = A 1 * B 0 := by rw [cross] at h; linarith
  have hs : ∀ (c : ℝ) (p : ℝ²), (c • p) 0 = c * p 0 ∧ (c • p) 1 = c * p 1 := fun c p =>
    ⟨rfl, rfl⟩
  by_cases h0 : A 0 = 0
  · have h1 : A 1 ≠ 0 := by
      intro h1
      refine hA (ext_two ?_ ?_) <;> simp [h0, h1]
    have hB0 : B 0 = 0 := by
      rw [h0, zero_mul] at hco
      exact (mul_eq_zero.1 hco.symm).resolve_left h1
    refine ⟨B 1 / A 1, ext_two ?_ ?_⟩
    · rw [(hs _ _).1, hB0, h0, mul_zero]
    · rw [(hs _ _).2]; field_simp
  · refine ⟨B 0 / A 0, ext_two ?_ ?_⟩
    · rw [(hs _ _).1]; field_simp
    · rw [(hs _ _).2]; field_simp; linarith [hco]

/-! ## Sectors and their additivity -/

/-- `cross A ·` as a linear functional. -/
def crossL (A : ℝ²) : ℝ² →ₗ[ℝ] ℝ where
  toFun q := cross A q
  map_add' := cross_add_right A
  map_smul' c q := by simp only [cross_smul_right, RingHom.id_apply, smul_eq_mul]

@[simp] lemma crossL_apply (A q : ℝ²) : crossL A q = cross A q := rfl

lemma continuous_crossL (A : ℝ²) : Continuous (crossL A) := by
  have : (crossL A : ℝ² → ℝ) = fun q => A 0 * q 1 - A 1 * q 0 := rfl
  rw [this]
  fun_prop

lemma measurableSet_wedgeC (A B : ℝ²) : MeasurableSet (wedgeC A B) := by
  have h1 : MeasurableSet {q : ℝ² | 0 ≤ cross A q} :=
    measurableSet_le measurable_const (continuous_crossL A).measurable
  have h2 : MeasurableSet {q : ℝ² | cross B q ≤ 0} :=
    measurableSet_le (continuous_crossL B).measurable measurable_const
  exact h1.inter h2

/-- A line through the origin is null. -/
theorem volume_setOf_cross_eq_zero {B : ℝ²} (hB : B ≠ 0) :
    volume {q : ℝ² | cross B q = 0} = 0 := by
  have hker : {q : ℝ² | cross B q = 0} = (LinearMap.ker (crossL B) : Set ℝ²) := by
    ext q; simp [LinearMap.mem_ker]
  rw [hker]
  refine Measure.addHaar_submodule volume _ ?_
  intro htop
  -- the rotation of `B` by `π/2` has `cross B · ≠ 0`
  obtain ⟨w, hw⟩ : ∃ w : ℝ², w = pt (-B 1) (B 0) := ⟨_, rfl⟩
  have hval : cross B w = B 0 * B 0 + B 1 * B 1 := by rw [hw, cross, pt_zero, pt_one]; ring
  have hmem : w ∈ LinearMap.ker (crossL B) := by rw [htop]; trivial
  rw [LinearMap.mem_ker, crossL_apply, hval] at hmem
  have h0 : B 0 = 0 := by nlinarith [sq_nonneg (B 0), sq_nonneg (B 1)]
  have h1 : B 1 = 0 := by nlinarith [sq_nonneg (B 0), sq_nonneg (B 1)]
  exact hB (ext_two (by simp [h0]) (by simp [h1]))

/-- The sector of `K` between the rays through `A` and `B`. -/
def sector (K : Set ℝ²) (A B : ℝ²) : Set ℝ² := K ∩ wedgeC A B

/-- **Additivity of the sector areas.** -/
theorem volume_sector_add {K : Set ℝ²} (hKm : MeasurableSet K) {A B C : ℝ²} (hB : B ≠ 0)
    (hAB : 0 ≤ cross A B) (hBC : 0 ≤ cross B C) (hAC : 0 < cross A C) :
    volume (sector K A C) = volume (sector K A B) + volume (sector K B C) := by
  have hm : ∀ X Y : ℝ², MeasurableSet (sector K X Y) := fun X Y =>
    hKm.inter (measurableSet_wedgeC X Y)
  -- the union covers
  have hcov : sector K A C ⊆ sector K A B ∪ sector K B C := by
    rintro q ⟨hq, hw⟩
    rcases wedgeC_subset_union A B C hw with h | h
    · exact Or.inl ⟨hq, h⟩
    · exact Or.inr ⟨hq, h⟩
  -- each piece is inside, up to a null line
  have hnull : volume {q : ℝ² | cross B q = 0} = 0 := volume_setOf_cross_eq_zero hB
  have hA : A ≠ 0 := by
    intro hA0
    rw [hA0] at hAC
    simp [cross] at hAC
  have hsub1 : volume (sector K A B \ sector K A C) = 0 := by
    rcases eq_or_lt_of_le hAB with h | h
    · obtain ⟨μ, hμ⟩ := exists_smul_of_cross_eq_zero hA h.symm
      have hμ0 : 0 < μ := by
        rcases lt_trichotomy μ 0 with hm0 | hm0 | hm0
        · exfalso
          rw [hμ, cross_smul_left] at hBC
          nlinarith
        · exact absurd (by rw [hμ, hm0, zero_smul]) hB
        · exact hm0
      have hline : wedgeC A B ⊆ {q : ℝ² | cross A q = 0} := wedgeC_subset_line hμ0 hμ
      exact measure_mono_null (fun q hq => hline hq.1.2) (volume_setOf_cross_eq_zero hA)
    · refine measure_mono_null (fun q hq => absurd ?_ hq.2) (measure_empty (μ := volume))
      exact ⟨hq.1.1, wedgeC_subset_left h hBC hAC hq.1.2⟩
  have hsub2 : volume (sector K B C \ sector K A C) = 0 := by
    rcases eq_or_lt_of_le hBC with h | h
    · obtain ⟨ν, hν⟩ := exists_smul_of_cross_eq_zero hB h.symm
      have hν0 : 0 < ν := by
        rcases lt_trichotomy ν 0 with hm0 | hm0 | hm0
        · exfalso
          rw [hν, cross_smul_right] at hAC
          nlinarith
        · exfalso
          rw [hν, hm0, zero_smul] at hAC
          simp [cross] at hAC
        · exact hm0
      have hline : wedgeC B C ⊆ {q : ℝ² | cross B q = 0} := wedgeC_subset_line hν0 hν
      exact measure_mono_null (fun q hq => hline hq.1.2) (volume_setOf_cross_eq_zero hB)
    · refine measure_mono_null (fun q hq => absurd ?_ hq.2) (measure_empty (μ := volume))
      exact ⟨hq.1.1, wedgeC_subset_right hAB h hAC hq.1.2⟩
  -- disjointness up to a null set
  have hdisj : volume (sector K A B ∩ sector K B C) = 0 :=
    measure_mono_null (fun q hq => wedgeC_inter_subset A B C ⟨hq.1.2, hq.2.2⟩) hnull
  -- combine
  have h1 : volume (sector K A B ∪ sector K B C) = volume (sector K A C) := by
    refine le_antisymm ?_ (measure_mono hcov)
    calc volume (sector K A B ∪ sector K B C)
        ≤ volume (sector K A C ∪ (sector K A B \ sector K A C)
            ∪ (sector K B C \ sector K A C)) := by
          refine measure_mono ?_
          rintro q (hq | hq)
          · by_cases hc : q ∈ sector K A C
            · exact Or.inl (Or.inl hc)
            · exact Or.inl (Or.inr ⟨hq, hc⟩)
          · by_cases hc : q ∈ sector K A C
            · exact Or.inl (Or.inl hc)
            · exact Or.inr ⟨hq, hc⟩
      _ ≤ volume (sector K A C ∪ (sector K A B \ sector K A C))
            + volume (sector K B C \ sector K A C) := measure_union_le _ _
      _ ≤ volume (sector K A C) + volume (sector K A B \ sector K A C)
            + volume (sector K B C \ sector K A C) := by
          gcongr
          exact measure_union_le _ _
      _ = volume (sector K A C) := by rw [hsub1, hsub2]; simp
  have h2 := measure_union_add_inter (μ := volume) (sector K A B) (hm B C)
  rw [hdisj, add_zero] at h2
  rw [← h1]
  exact h2

end Sofa
