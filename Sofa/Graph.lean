/-
# Sofa/Graph.lean — piecewise-affine functions of one real variable (blueprint §11, G1)

* `tieSet`: where two members of a finite family of affine functions agree (finite when the
  family is pairwise distinct);
* a continuous selection of the family is locally one of its members off the tie set
  (`eventuallyEq_of_selection`), hence differentiable there;
* **FTC for selections** (`sub_eq_sum_mul_measureReal_activeSet`) and the a.e. partition of `ℝ`
  into active sets (`sum_volume_activeSet_inter`);
* calculus of `Finset.inf'` / `Finset.sup'` at a strict extremizer, and their sup-norm Lipschitz
  bounds;
* Cavalieri's principle for regions between two graphs (`volume_between`).

STATUS: in progress (2026-09-17, Opus 5).
-/
import Sofa.Nef

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

/-! ## Continuous selections of finitely many affine functions -/

section Selection

variable {ι : Type*}

/-- Pairwise distinctness of the affine functions `x ↦ a i + b i * x`, `i ∈ S`. -/
def AffDistinct (S : Finset ι) (a b : ι → ℝ) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → a i ≠ a j ∨ b i ≠ b j

/-- The tie set of the family: points where two distinct members agree. -/
def tieSet (S : Finset ι) (a b : ι → ℝ) : Set ℝ :=
  {x | ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧ a i + b i * x = a j + b j * x}

/-- The active set of the `i`-th piece of `g`. -/
def activeSet (g : ℝ → ℝ) (a b : ι → ℝ) (i : ι) : Set ℝ := {x | g x = a i + b i * x}

variable {S : Finset ι} {a b : ι → ℝ} {g : ℝ → ℝ}

lemma tieSet_finite (h : AffDistinct S a b) : (tieSet S a b).Finite := by
  have hsub : tieSet S a b ⊆ ⋃ i ∈ S, ⋃ j ∈ S, {x | i ≠ j ∧ a i + b i * x = a j + b j * x} := by
    rintro x ⟨i, hi, j, hj, hij, hx⟩
    exact mem_iUnion₂.2 ⟨i, hi, mem_iUnion₂.2 ⟨j, hj, hij, hx⟩⟩
  refine Set.Finite.subset (Set.Finite.biUnion S.finite_toSet fun i hi =>
    Set.Finite.biUnion S.finite_toSet fun j hj => ?_) hsub
  by_cases hij : i = j
  · refine Set.finite_empty.subset fun x hx => ?_
    exact hx.1 hij
  by_cases hb : b i = b j
  · have ha : a i ≠ a j := (h i hi j hj hij).resolve_right (not_not.2 hb)
    refine Set.finite_empty.subset fun x hx => ?_
    obtain ⟨-, hx⟩ := hx
    rw [hb] at hx
    exact ha (by linarith)
  · refine (Set.finite_singleton ((a j - a i) / (b i - b j))).subset fun x hx => ?_
    obtain ⟨-, hx⟩ := hx
    rw [mem_singleton_iff, eq_div_iff (sub_ne_zero.2 hb)]
    linarith

lemma volume_tieSet (h : AffDistinct S a b) : volume (tieSet S a b) = 0 :=
  (tieSet_finite h).measure_zero volume

lemma isClosed_activeSet (hg : Continuous g) (i : ι) : IsClosed (activeSet g a b i) :=
  isClosed_eq hg (continuous_const.add (continuous_const.mul continuous_id))

lemma measurableSet_activeSet (hg : Continuous g) (i : ι) : MeasurableSet (activeSet g a b i) :=
  (isClosed_activeSet hg i).measurableSet

lemma eq_of_mem_activeSet {x : ℝ} (hx : x ∉ tieSet S a b) {i j : ι} (hi : i ∈ S) (hj : j ∈ S)
    (hxi : x ∈ activeSet g a b i) (hxj : x ∈ activeSet g a b j) : i = j := by
  by_contra hij
  exact hx ⟨i, hi, j, hj, hij, hxi.symm.trans hxj⟩

/-- A continuous selection is locally one affine piece away from the tie set. -/
lemma eventuallyEq_of_selection (hg : Continuous g)
    (hsel : ∀ x, ∃ i ∈ S, x ∈ activeSet g a b i) {x : ℝ} (hx : x ∉ tieSet S a b) {i : ι}
    (hi : i ∈ S) (hxi : x ∈ activeSet g a b i) :
    g =ᶠ[𝓝 x] fun y => a i + b i * y := by
  have key : ∀ᶠ y in 𝓝 x, ∀ j ∈ S, j ≠ i → g y ≠ a j + b j * y := by
    rw [eventually_all_finset]
    intro j hj
    by_cases hji : j = i
    · exact Eventually.of_forall fun _ h => absurd hji h
    · have hne : g x ≠ a j + b j * x := fun h => hx ⟨i, hi, j, hj, Ne.symm hji, hxi.symm.trans h⟩
      have hc : Continuous fun y => g y - (a j + b j * y) := by fun_prop
      have hne' : g x - (a j + b j * x) ≠ 0 := sub_ne_zero.2 hne
      exact (hc.continuousAt.eventually_ne hne').mono fun _ h _ => sub_ne_zero.1 h
  filter_upwards [key] with y hy
  obtain ⟨k, hk, hyk⟩ := hsel y
  by_cases hki : k = i
  · rw [← hki]; exact hyk
  · exact absurd hyk (hy k hk hki)

lemma hasDerivAt_of_selection (hg : Continuous g)
    (hsel : ∀ x, ∃ i ∈ S, x ∈ activeSet g a b i) {x : ℝ} (hx : x ∉ tieSet S a b) {i : ι}
    (hi : i ∈ S) (hxi : x ∈ activeSet g a b i) : HasDerivAt g (b i) x := by
  have h1 : HasDerivAt (fun y => a i + b i * y) (b i) x := by
    simpa using ((hasDerivAt_id x).const_mul (b i)).const_add (a i)
  exact h1.congr_of_eventuallyEq (eventuallyEq_of_selection hg hsel hx hi hxi)

/-- The active sets of a continuous selection partition `ℝ` up to a null set. -/
theorem sum_volume_activeSet_inter (hS : AffDistinct S a b) (hg : Continuous g)
    (hsel : ∀ x, ∃ i ∈ S, x ∈ activeSet g a b i) {A : Set ℝ} (hA : MeasurableSet A) :
    ∑ i ∈ S, volume (activeSet g a b i ∩ A) = volume A := by
  have hT := volume_tieSet hS
  have hTm : MeasurableSet (tieSet S a b) := (tieSet_finite hS).measurableSet
  have e1 : ∀ i, volume (activeSet g a b i ∩ A) =
      volume ((activeSet g a b i \ tieSet S a b) ∩ A) := by
    intro i
    refine measure_congr ?_
    exact ((sdiff_null_ae_eq_self hT).symm).inter (ae_eq_refl A)
  have hdisj : (S : Set ι).PairwiseDisjoint
      fun i => (activeSet g a b i \ tieSet S a b) ∩ A := by
    intro i hi j hj hij
    refine Set.disjoint_left.2 fun z hzi hzj => hij ?_
    exact eq_of_mem_activeSet hzi.1.2 hi hj hzi.1.1 hzj.1.1
  have hunion : ⋃ i ∈ S, (activeSet g a b i \ tieSet S a b) ∩ A = A \ tieSet S a b := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, -, ⟨-, hz2⟩, hz3⟩ := mem_iUnion₂.1 hz
      exact ⟨hz3, hz2⟩
    · rintro ⟨hzA, hzT⟩
      obtain ⟨i, hi, hzi⟩ := hsel z
      exact mem_iUnion₂.2 ⟨i, hi, ⟨hzi, hzT⟩, hzA⟩
  rw [Finset.sum_congr rfl fun i _ => e1 i, ← measure_biUnion_finset hdisj
    (fun i _ => ((measurableSet_activeSet hg i).diff hTm).inter hA), hunion,
    measure_sdiff_null hT]

theorem sum_measureReal_activeSet_inter (hS : AffDistinct S a b) (hg : Continuous g)
    (hsel : ∀ x, ∃ i ∈ S, x ∈ activeSet g a b i) {A : Set ℝ} (hA : MeasurableSet A)
    (hAf : volume A ≠ ⊤) :
    ∑ i ∈ S, volume.real (activeSet g a b i ∩ A) = volume.real A := by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_sum fun i _ => ne_top_of_le_ne_top hAf (measure_mono inter_subset_right),
    sum_volume_activeSet_inter hS hg hsel hA]

/-- **FTC for continuous selections of affine functions.** -/
theorem sub_eq_sum_mul_measureReal_activeSet (hS : AffDistinct S a b) (hg : Continuous g)
    (hsel : ∀ x, ∃ i ∈ S, x ∈ activeSet g a b i) {x y : ℝ} (hxy : x ≤ y) :
    g y - g x = ∑ i ∈ S, b i * volume.real (activeSet g a b i ∩ Icc x y) := by
  set φ : ℝ → ℝ := fun z => ∑ i ∈ S, (activeSet g a b i).indicator (fun _ => b i) z with hφdef
  have hmeas : ∀ i, MeasurableSet (activeSet g a b i) := measurableSet_activeSet hg
  have hφ : ∀ z ∉ tieSet S a b, ∀ i ∈ S, z ∈ activeSet g a b i → φ z = b i := by
    intro z hz i hi hzi
    simp only [hφdef]
    rw [Finset.sum_eq_single_of_mem i hi]
    · exact indicator_of_mem hzi _
    · intro j hj hji
      have : z ∉ activeSet g a b j := fun hzj => hji (eq_of_mem_activeSet hz hj hi hzj hzi)
      exact indicator_of_notMem this _
  have hderiv : ∀ z ∈ Ioo x y \ tieSet S a b, HasDerivAt g (φ z) z := by
    rintro z ⟨-, hz⟩
    obtain ⟨i, hi, hzi⟩ := hsel z
    rw [hφ z hz i hi hzi]
    exact hasDerivAt_of_selection hg hsel hz hi hzi
  have hint : ∀ i, IntervalIntegrable ((activeSet g a b i).indicator fun _ => b i) volume x y := by
    intro i
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hxy]
    exact (integrableOn_const measure_Ioc_lt_top.ne).indicator (hmeas i)
  have hsum : IntervalIntegrable φ volume x y := by
    have e : φ = ∑ i ∈ S, (activeSet g a b i).indicator fun _ => b i := by
      ext z
      simp [hφdef, Finset.sum_apply]
    rw [e]
    exact IntervalIntegrable.sum S fun i _ => hint i
  have hftc := integral_eq_of_hasDerivAt_off_countable_of_le g φ hxy
    (tieSet_finite hS).countable hg.continuousOn hderiv hsum
  rw [← hftc, hφdef, intervalIntegral.integral_finsetSum fun i _ => hint i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_of_le hxy, integral_indicator_const _ (hmeas i), smul_eq_mul,
    mul_comm, measureReal_restrict_apply (hmeas i)]
  congr 1
  simp only [measureReal_def]
  congr 1
  exact measure_congr ((ae_eq_refl _).inter Ioc_ae_eq_Icc)

end Selection

/-! ## `Finset.inf'` / `Finset.sup'` near a strict extremizer -/

section Extremizer

variable {ι α : Type*} [TopologicalSpace α] {D : Finset ι} (hD : D.Nonempty)
  {F : ι → α → ℝ} {a₀ : α}

lemma eventually_inf'_eq (hF : ∀ i ∈ D, ContinuousAt (F i) a₀) {i₀ : ι} (hi₀ : i₀ ∈ D)
    (hmin : ∀ i ∈ D, i ≠ i₀ → F i₀ a₀ < F i a₀) :
    ∀ᶠ a in 𝓝 a₀, D.inf' hD (fun i => F i a) = F i₀ a := by
  have h1 : ∀ᶠ a in 𝓝 a₀, ∀ i ∈ D, i ≠ i₀ → F i₀ a < F i a := by
    rw [eventually_all_finset]
    intro i hi
    by_cases h : i = i₀
    · exact Eventually.of_forall fun _ h' => absurd h h'
    · exact ((hF i₀ hi₀).eventually_lt (hF i hi) (hmin i hi h)).mono fun _ h' _ => h'
  filter_upwards [h1] with a ha
  refine le_antisymm (Finset.inf'_le _ hi₀) ((Finset.le_inf'_iff _ _).2 fun i hi => ?_)
  by_cases h : i = i₀
  · rw [h]
  · exact (ha i hi h).le

lemma eventually_sup'_eq (hF : ∀ i ∈ D, ContinuousAt (F i) a₀) {i₀ : ι} (hi₀ : i₀ ∈ D)
    (hmax : ∀ i ∈ D, i ≠ i₀ → F i a₀ < F i₀ a₀) :
    ∀ᶠ a in 𝓝 a₀, D.sup' hD (fun i => F i a) = F i₀ a := by
  have h1 : ∀ᶠ a in 𝓝 a₀, ∀ i ∈ D, i ≠ i₀ → F i a < F i₀ a := by
    rw [eventually_all_finset]
    intro i hi
    by_cases h : i = i₀
    · exact Eventually.of_forall fun _ h' => absurd h h'
    · exact ((hF i hi).eventually_lt (hF i₀ hi₀) (hmax i hi h)).mono fun _ h' _ => h'
  filter_upwards [h1] with a ha
  refine le_antisymm ((Finset.sup'_le_iff _ _).2 fun i hi => ?_) (Finset.le_sup' (fun i => F i a) hi₀)
  by_cases h : i = i₀
  · rw [h]
  · exact (ha i hi h).le

end Extremizer

section Deriv

variable {ι : Type*} {D : Finset ι} (hD : D.Nonempty) {F : ι → ℝ → ℝ} {F' : ι → ℝ} {ε₀ : ℝ}

lemma hasDerivAt_inf' (hF : ∀ i ∈ D, HasDerivAt (F i) (F' i) ε₀) {i₀ : ι} (hi₀ : i₀ ∈ D)
    (hmin : ∀ i ∈ D, i ≠ i₀ → F i₀ ε₀ < F i ε₀) :
    HasDerivAt (fun ε => D.inf' hD fun i => F i ε) (F' i₀) ε₀ :=
  (hF i₀ hi₀).congr_of_eventuallyEq
    (eventually_inf'_eq hD (fun i hi => (hF i hi).continuousAt) hi₀ hmin)

lemma hasDerivAt_sup' (hF : ∀ i ∈ D, HasDerivAt (F i) (F' i) ε₀) {i₀ : ι} (hi₀ : i₀ ∈ D)
    (hmax : ∀ i ∈ D, i ≠ i₀ → F i ε₀ < F i₀ ε₀) :
    HasDerivAt (fun ε => D.sup' hD fun i => F i ε) (F' i₀) ε₀ :=
  (hF i₀ hi₀).congr_of_eventuallyEq
    (eventually_sup'_eq hD (fun i hi => (hF i hi).continuousAt) hi₀ hmax)

variable {f g : ℝ → ℝ} {f' g' : ℝ}

lemma hasDerivAt_min_left (hf : HasDerivAt f f' ε₀) (hg : HasDerivAt g g' ε₀)
    (h : f ε₀ < g ε₀) : HasDerivAt (fun ε => min (f ε) (g ε)) f' ε₀ :=
  hf.congr_of_eventuallyEq
    ((hf.continuousAt.eventually_lt hg.continuousAt h).mono fun _ h => min_eq_left h.le)

lemma hasDerivAt_min_right (hf : HasDerivAt f f' ε₀) (hg : HasDerivAt g g' ε₀)
    (h : g ε₀ < f ε₀) : HasDerivAt (fun ε => min (f ε) (g ε)) g' ε₀ :=
  hg.congr_of_eventuallyEq
    ((hg.continuousAt.eventually_lt hf.continuousAt h).mono fun _ h => min_eq_right h.le)

lemma hasDerivAt_max_zero_of_pos (hf : HasDerivAt f f' ε₀) (h : 0 < f ε₀) :
    HasDerivAt (fun ε => max (f ε) 0) f' ε₀ :=
  hf.congr_of_eventuallyEq
    ((continuousAt_const.eventually_lt hf.continuousAt h).mono fun _ h => max_eq_left h.le)

lemma hasDerivAt_max_zero_of_neg (hf : HasDerivAt f f' ε₀) (h : f ε₀ < 0) :
    HasDerivAt (fun ε => max (f ε) 0) 0 ε₀ :=
  (hasDerivAt_const ε₀ (0 : ℝ)).congr_of_eventuallyEq
    ((hf.continuousAt.eventually_lt continuousAt_const h).mono fun _ h => max_eq_right h.le)

end Deriv

/-! ## Sup-norm Lipschitz bounds -/

section Lipschitz

variable {ι : Type*} {D : Finset ι} (hD : D.Nonempty) {F G : ι → ℝ} {c : ℝ}

lemma abs_inf'_sub_inf'_le (h : ∀ i ∈ D, |F i - G i| ≤ c) :
    |D.inf' hD F - D.inf' hD G| ≤ c := by
  obtain ⟨i, hi, hFi⟩ := D.exists_mem_eq_inf' hD F
  obtain ⟨j, hj, hGj⟩ := D.exists_mem_eq_inf' hD G
  have h1 : D.inf' hD G ≤ G i := Finset.inf'_le G hi
  have h2 : D.inf' hD F ≤ F j := Finset.inf'_le F hj
  have h3 := abs_le.1 (h i hi)
  have h4 := abs_le.1 (h j hj)
  rw [abs_le]
  constructor <;> linarith

lemma abs_sup'_sub_sup'_le (h : ∀ i ∈ D, |F i - G i| ≤ c) :
    |D.sup' hD F - D.sup' hD G| ≤ c := by
  obtain ⟨i, hi, hFi⟩ := D.exists_mem_eq_sup' hD F
  obtain ⟨j, hj, hGj⟩ := D.exists_mem_eq_sup' hD G
  have h1 : G i ≤ D.sup' hD G := Finset.le_sup' G hi
  have h2 : F j ≤ D.sup' hD F := Finset.le_sup' F hj
  have h3 := abs_le.1 (h i hi)
  have h4 := abs_le.1 (h j hj)
  rw [abs_le]
  constructor <;> linarith

end Lipschitz

/-! ## Cavalieri's principle for regions between two graphs -/

lemma measurable_coord (i : Fin 2) : Measurable fun p : ℝ² => p i :=
  (EuclideanSpace.proj i : ℝ² →L[ℝ] ℝ).continuous.measurable

lemma smul_u_zero_add_smul_v_zero (x r : ℝ) :
    (x • u 0 + r • v 0) 0 = x ∧ (x • u 0 + r • v 0) 1 = r := by
  constructor <;> simp [u, v]

theorem volume_between_Icc {lo hi : ℝ → ℝ} (hlo : Measurable lo) (hhi : Measurable hi) :
    volume {p : ℝ² | lo (p 0) ≤ p 1 ∧ p 1 ≤ hi (p 0)} = ∫⁻ x, ENNReal.ofReal (hi x - lo x) := by
  have hY : MeasurableSet {p : ℝ² | lo (p 0) ≤ p 1 ∧ p 1 ≤ hi (p 0)} :=
    (measurableSet_le (hlo.comp (measurable_coord 0)) (measurable_coord 1)).inter
      (measurableSet_le (measurable_coord 1) (hhi.comp (measurable_coord 0)))
  rw [volume_eq_lintegral_slice 0 hY]
  refine lintegral_congr fun x => ?_
  have : slice {p : ℝ² | lo (p 0) ≤ p 1 ∧ p 1 ≤ hi (p 0)} 0 x = Icc (lo x) (hi x) := by
    ext r
    obtain ⟨e0, e1⟩ := smul_u_zero_add_smul_v_zero x r
    simp only [slice, mem_ofPred_eq, e0, e1, mem_Icc]
  rw [this, Real.volume_Icc]

theorem volume_between_Ico {lo hi : ℝ → ℝ} (hlo : Measurable lo) (hhi : Measurable hi) :
    volume {p : ℝ² | lo (p 0) ≤ p 1 ∧ p 1 < hi (p 0)} = ∫⁻ x, ENNReal.ofReal (hi x - lo x) := by
  have hY : MeasurableSet {p : ℝ² | lo (p 0) ≤ p 1 ∧ p 1 < hi (p 0)} :=
    (measurableSet_le (hlo.comp (measurable_coord 0)) (measurable_coord 1)).inter
      (measurableSet_lt (measurable_coord 1) (hhi.comp (measurable_coord 0)))
  rw [volume_eq_lintegral_slice 0 hY]
  refine lintegral_congr fun x => ?_
  have : slice {p : ℝ² | lo (p 0) ≤ p 1 ∧ p 1 < hi (p 0)} 0 x = Ico (lo x) (hi x) := by
    ext r
    obtain ⟨e0, e1⟩ := smul_u_zero_add_smul_v_zero x r
    simp only [slice, mem_ofPred_eq, e0, e1, mem_Ico]
  rw [this, Real.volume_Ico]

lemma ofReal_eq_ofReal_max_zero (a : ℝ) : ENNReal.ofReal a = ENNReal.ofReal (max a 0) := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

theorem measureReal_between_Icc {lo hi : ℝ → ℝ} (hlo : Measurable lo) (hhi : Measurable hi)
    (hint : Integrable fun x => max (hi x - lo x) 0) :
    volume.real {p : ℝ² | lo (p 0) ≤ p 1 ∧ p 1 ≤ hi (p 0)} = ∫ x, max (hi x - lo x) 0 := by
  rw [measureReal_def, volume_between_Icc hlo hhi, integral_eq_lintegral_of_nonneg_ae
    (f := fun x => max (hi x - lo x) 0) (Eventually.of_forall fun x => le_max_right _ _)
    hint.aestronglyMeasurable]
  simp_rw [← ofReal_eq_ofReal_max_zero]

theorem measureReal_between_Ico {lo hi : ℝ → ℝ} (hlo : Measurable lo) (hhi : Measurable hi)
    (hint : Integrable fun x => max (hi x - lo x) 0) :
    volume.real {p : ℝ² | lo (p 0) ≤ p 1 ∧ p 1 < hi (p 0)} = ∫ x, max (hi x - lo x) 0 := by
  rw [measureReal_def, volume_between_Ico hlo hhi, integral_eq_lintegral_of_nonneg_ae
    (f := fun x => max (hi x - lo x) 0) (Eventually.of_forall fun x => le_max_right _ _)
    hint.aestronglyMeasurable]
  simp_rw [← ofReal_eq_ofReal_max_zero]

/-! ## Lines as graphs over the `x`-axis -/

/-- The line `{⟪p, u_s⟫ = c}` as the graph of a function of `x` (meaningful for `sin s ≠ 0`). -/
def lineFn (s c x : ℝ) : ℝ := (c - x * cos s) / sin s

lemma lineFn_eq (s c x : ℝ) : lineFn s c x = c / sin s + -(cos s / sin s) * x := by
  unfold lineFn; ring

lemma continuous_lineFn (s c : ℝ) : Continuous (lineFn s c) := by
  unfold lineFn; fun_prop

lemma le_lineFn_iff {s : ℝ} (hs : 0 < sin s) (c : ℝ) (p : ℝ²) :
    p 1 ≤ lineFn s c (p 0) ↔ ⟪p, u s⟫ ≤ c := by
  rw [lineFn, le_div_iff₀ hs, inner_u_decomp]
  constructor <;> intro h <;> linarith

lemma lt_lineFn_iff {s : ℝ} (hs : 0 < sin s) (c : ℝ) (p : ℝ²) :
    p 1 < lineFn s c (p 0) ↔ ⟪p, u s⟫ < c := by
  rw [lineFn, lt_div_iff₀ hs, inner_u_decomp]
  constructor <;> intro h <;> linarith

lemma lineFn_le_iff {s : ℝ} (hs : 0 < sin s) (c : ℝ) (p : ℝ²) :
    lineFn s c (p 0) ≤ p 1 ↔ c ≤ ⟪p, u s⟫ := by
  rw [lineFn, div_le_iff₀ hs, inner_u_decomp]
  constructor <;> intro h <;> linarith

lemma lineFn_lt_iff {s : ℝ} (hs : 0 < sin s) (c : ℝ) (p : ℝ²) :
    lineFn s c (p 0) < p 1 ↔ c < ⟪p, u s⟫ := by
  rw [lineFn, div_lt_iff₀ hs, inner_u_decomp]
  constructor <;> intro h <;> linarith

lemma lineFn_add (s c d x : ℝ) : lineFn s (c + d) x = lineFn s c x + d / sin s := by
  unfold lineFn; ring

lemma lineFn_mono {s : ℝ} (hs : 0 < sin s) {c c' : ℝ} (h : c ≤ c') (x : ℝ) :
    lineFn s c x ≤ lineFn s c' x := by
  unfold lineFn
  exact div_le_div_of_nonneg_right (by linarith) hs.le

lemma lineFn_strictMono {s : ℝ} (hs : 0 < sin s) {c c' : ℝ} (h : c < c') (x : ℝ) :
    lineFn s c x < lineFn s c' x := by
  unfold lineFn
  exact div_lt_div_of_pos_right (by linarith) hs

lemma lineFn_translate {s : ℝ} (hs : sin s ≠ 0) (c : ℝ) (w : ℝ²) (x : ℝ) :
    lineFn s (c + ⟪w, u s⟫) x = lineFn s c (x - w 0) + w 1 := by
  rw [inner_u_decomp]
  unfold lineFn
  field_simp
  ring

lemma abs_lineFn_sub_lineFn {s : ℝ} (hs : 0 < sin s) (c c' x : ℝ) :
    |lineFn s c x - lineFn s c' x| = |c - c'| / sin s := by
  unfold lineFn
  rw [← sub_div, abs_div, abs_of_pos hs]
  ring_nf

/-- `cot` is strictly decreasing on `(0, π)`. -/
lemma cot_lt_cot {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < π) :
    cos t / sin t < cos s / sin s := by
  have hss : 0 < sin s := sin_pos_of_pos_of_lt_pi hs (hst.trans ht)
  have hts : 0 < sin t := sin_pos_of_pos_of_lt_pi (hs.trans hst) ht
  rw [div_lt_div_iff₀ hts hss]
  have : 0 < sin (t - s) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [sin_sub] at this
  linarith

end Sofa
