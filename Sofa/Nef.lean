/-
# Sofa/Nef.lean — Nef polygons: slices, Cavalieri, and the area derivative (Baek §3.1)

Replaces Baek's Thm 3.1.2 (cell decomposition) by a slice argument (blueprint §10, D1–D2):
* `rotCoord t : ℝ × ℝ → ℝ²`, `(s, r) ↦ s u_t + r v_t`, is measure preserving; Cavalieri's
  principle in these coordinates (`volume_eq_lintegral_slice`);
* half-planes `HP` and Nef sets `nefSet E H` over a finite index type;
* the slices of two Nef sets with the same angles differ only near the moving endpoints
  (`volume_slice_symmDiff_le`);
* **area derivative** (`hasDerivWithinAt_volume_pushed`): pushing the `i`-th defining half-plane
  of a bounded Nef set with monotone `E` outwards by `δ ≥ 0` has right derivative at `δ = 0` equal
  to the length of the slice of `nefSet (switchE E i) H` along the boundary line of `H i`
  (the part of that line where switching `H i` on changes membership).  Only a simplicity
  condition on half-planes *parallel* to `H i` is needed.

STATUS: [PROOF-C-local][AXIOM-CHECK] (2026-09-17, Opus 5) — 0 sorry; axioms
`propext, Classical.choice, Quot.sound` (see `Sofa/Check.lean`).
-/
import Sofa.Vertex

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace symmDiff

namespace Sofa

/-! ## Rotated coordinates and Cavalieri -/

/-- Rotated coordinates `(s, r) ↦ s u_t + r v_t`. -/
def rotCoord (t : ℝ) (q : ℝ × ℝ) : ℝ² := q.1 • u t + q.2 • v t

lemma rotCoord_eq (t : ℝ) (q : ℝ × ℝ) :
    rotCoord t q = (EuclideanGeometry.o : Orientation ℝ ℝ² (Fin 2)).rotation (t : Real.Angle)
      ((WithLp.toLp 2 (MeasurableEquiv.finTwoArrow.symm q) : ℝ²)) := by
  rw [← rot_eq_rotation]
  ext i
  fin_cases i <;> simp [rotCoord, rot, u, v, MeasurableEquiv.finTwoArrow] <;> ring

lemma measurePreserving_rotCoord (t : ℝ) :
    MeasurePreserving (rotCoord t) (volume : Measure (ℝ × ℝ)) volume := by
  have h1 := (volume_preserving_finTwoArrow ℝ).symm
  have h2 := PiLp.volume_preserving_toLp (Fin 2)
  have h3 :=
    ((EuclideanGeometry.o : Orientation ℝ ℝ² (Fin 2)).rotation (t : Real.Angle)).measurePreserving
  have := h3.comp (h2.comp h1)
  have e : rotCoord t = ⇑((EuclideanGeometry.o : Orientation ℝ ℝ² (Fin 2)).rotation
      (t : Real.Angle)) ∘ WithLp.toLp 2 ∘ ⇑MeasurableEquiv.finTwoArrow.symm :=
    funext fun q => rotCoord_eq t q
  rw [e]
  exact this

lemma measurable_rotCoord (t : ℝ) : Measurable (rotCoord t) :=
  (measurePreserving_rotCoord t).measurable

/-- The slice `{r | s u_t + r v_t ∈ Y}` of `Y` along the line `l(t, s)`. -/
def slice (Y : Set ℝ²) (t s : ℝ) : Set ℝ := {r : ℝ | s • u t + r • v t ∈ Y}

/-- **Cavalieri's principle** in rotated coordinates. -/
theorem volume_eq_lintegral_slice (t : ℝ) {Y : Set ℝ²} (hY : MeasurableSet Y) :
    volume Y = ∫⁻ s, volume (slice Y t s) := by
  rw [← (measurePreserving_rotCoord t).measure_preimage hY.nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_apply ((measurable_rotCoord t) hY)]
  rfl

lemma cos_sub_comm (a b : ℝ) : cos (a - b) = cos (b - a) := by rw [← cos_neg, neg_sub]

lemma inner_rotCoord_u (t θ s r : ℝ) :
    ⟪s • u t + r • v t, u θ⟫ = s * cos (θ - t) + r * sin (θ - t) := by
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u_eq_cos,
    inner_v_u_eq_sin, cos_sub_comm]

/-! ## Half-planes and Nef sets -/

/-- A half-plane `{p | ⟪p, u θ⟫ ≤ c}` (`isOpen = false`) or `{p | ⟪p, u θ⟫ < c}`. -/
structure HP where
  θ : ℝ
  c : ℝ
  isOpen : Bool

namespace HP

/-- Membership in a half-plane. -/
def mem (H : HP) (p : ℝ²) : Prop := cond H.isOpen (⟪p, u H.θ⟫ < H.c) (⟪p, u H.θ⟫ ≤ H.c)

/-- The same half-plane with a new offset. -/
def withOffset (H : HP) (c : ℝ) : HP := ⟨H.θ, c, H.isOpen⟩

@[simp] lemma withOffset_θ (H : HP) (c : ℝ) : (H.withOffset c).θ = H.θ := rfl
@[simp] lemma withOffset_c (H : HP) (c : ℝ) : (H.withOffset c).c = c := rfl
@[simp] lemma withOffset_isOpen (H : HP) (c : ℝ) : (H.withOffset c).isOpen = H.isOpen := rfl

lemma measurableSet_mem (H : HP) : MeasurableSet {p : ℝ² | H.mem p} := by
  unfold mem
  cases H.isOpen
  · exact (isClosed_hpLe H.θ H.c).measurableSet
  · exact (isOpen_hpLt H.θ H.c).measurableSet

lemma mem_iff (H : HP) (p : ℝ²) :
    H.mem p ↔ ⟪p, u H.θ⟫ < H.c ∨ (H.isOpen = false ∧ ⟪p, u H.θ⟫ = H.c) := by
  unfold mem
  cases H.isOpen
  · simp only [cond_false, true_and]
    exact le_iff_lt_or_eq
  · simp

lemma mem_mono (H : HP) {c c' : ℝ} (hcc : c ≤ c') {p : ℝ²} (hp : (H.withOffset c).mem p) :
    (H.withOffset c').mem p := by
  rw [mem_iff] at hp ⊢
  simp only [withOffset_isOpen, withOffset_θ, withOffset_c] at hp ⊢
  rcases hp with h | ⟨ho, h⟩
  · left; linarith
  · rcases hcc.lt_or_eq with hlt | heq
    · left; linarith
    · right; exact ⟨ho, by rw [← heq]; exact h⟩

lemma mem_withOffset_of_inner {H : HP} {p : ℝ²} {c : ℝ} (hp : ⟪p, u H.θ⟫ < c) :
    (H.withOffset c).mem p := by
  rw [mem_iff]
  exact Or.inl hp

lemma mem_of_inner_lt {H : HP} {p : ℝ²} (hp : ⟪p, u H.θ⟫ < H.c) : H.mem p :=
  (mem_iff H p).2 (Or.inl hp)

lemma not_mem_of_inner {H : HP} {p : ℝ²} (hp : H.c < ⟪p, u H.θ⟫) : ¬ H.mem p := by
  rw [mem_iff]
  rintro (h | ⟨-, h⟩) <;> linarith

/-- The endpoint of the slice of `H` along `l(t, s)` (meaningful when `sin (θ - t) ≠ 0`). -/
def endpt (H : HP) (t s : ℝ) : ℝ := (H.c - s * cos (H.θ - t)) / sin (H.θ - t)

/-- Outside the interval between the two endpoints, slice memberships agree. -/
lemma mem_iff_of_not_mem_Icc {H H' : HP} (hθ : H.θ = H'.θ)
    {t s s' r : ℝ} (hsin : sin (H.θ - t) ≠ 0)
    (hr : r ∉ Icc (min (H.endpt t s) (H'.endpt t s')) (max (H.endpt t s) (H'.endpt t s'))) :
    H.mem (s • u t + r • v t) ↔ H'.mem (s' • u t + r • v t) := by
  have hθ' : H'.θ = H.θ := hθ.symm
  have hlt : ∀ (G : HP) (σ : ℝ), G.θ = H.θ → ⟪σ • u t + r • v t, u G.θ⟫ < G.c →
      G.mem (σ • u t + r • v t) := fun G σ _ h => mem_of_inner_lt h
  have hgt : ∀ (G : HP) (σ : ℝ), G.θ = H.θ → G.c < ⟪σ • u t + r • v t, u G.θ⟫ →
      ¬ G.mem (σ • u t + r • v t) := fun G σ _ h => not_mem_of_inner h
  unfold endpt at hr
  rw [hθ'] at hr
  simp only [mem_Icc, not_and_or, not_le] at hr
  rcases lt_or_gt_of_ne hsin with hneg | hpos
  · have key : ∀ (c σ : ℝ), (c - σ * cos (H.θ - t)) / sin (H.θ - t) < r ↔
        σ * cos (H.θ - t) + r * sin (H.θ - t) < c := fun c σ => by
      rw [div_lt_iff_of_neg hneg]; constructor <;> intro h <;> linarith
    have key' : ∀ (c σ : ℝ), r < (c - σ * cos (H.θ - t)) / sin (H.θ - t) ↔
        c < σ * cos (H.θ - t) + r * sin (H.θ - t) := fun c σ => by
      rw [lt_div_iff_of_neg hneg]; constructor <;> intro h <;> linarith
    rcases hr with hr | hr
    · have h1 := (key' H.c s).1 (lt_of_lt_of_le hr (min_le_left _ _))
      have h2 := (key' H'.c s').1 (lt_of_lt_of_le hr (min_le_right _ _))
      exact iff_of_false (hgt H s rfl (by rwa [inner_rotCoord_u]))
        (hgt H' s' hθ' (by rwa [inner_rotCoord_u, hθ']))
    · have h1 := (key H.c s).1 (lt_of_le_of_lt (le_max_left _ _) hr)
      have h2 := (key H'.c s').1 (lt_of_le_of_lt (le_max_right _ _) hr)
      exact iff_of_true (hlt H s rfl (by rwa [inner_rotCoord_u]))
        (hlt H' s' hθ' (by rwa [inner_rotCoord_u, hθ']))
  · have key : ∀ (c σ : ℝ), (c - σ * cos (H.θ - t)) / sin (H.θ - t) < r ↔
        c < σ * cos (H.θ - t) + r * sin (H.θ - t) := fun c σ => by
      rw [div_lt_iff₀ hpos]; constructor <;> intro h <;> linarith
    have key' : ∀ (c σ : ℝ), r < (c - σ * cos (H.θ - t)) / sin (H.θ - t) ↔
        σ * cos (H.θ - t) + r * sin (H.θ - t) < c := fun c σ => by
      rw [lt_div_iff₀ hpos]; constructor <;> intro h <;> linarith
    rcases hr with hr | hr
    · have h1 := (key' H.c s).1 (lt_of_lt_of_le hr (min_le_left _ _))
      have h2 := (key' H'.c s').1 (lt_of_lt_of_le hr (min_le_right _ _))
      exact iff_of_true (hlt H s rfl (by rwa [inner_rotCoord_u]))
        (hlt H' s' hθ' (by rwa [inner_rotCoord_u, hθ']))
    · have h1 := (key H.c s).1 (lt_of_le_of_lt (le_max_left _ _) hr)
      have h2 := (key H'.c s').1 (lt_of_le_of_lt (le_max_right _ _) hr)
      exact iff_of_false (hgt H s rfl (by rwa [inner_rotCoord_u]))
        (hgt H' s' hθ' (by rwa [inner_rotCoord_u, hθ']))

end HP

variable {ι : Type*}

/-- The Nef set `E(H₁, …, Hₙ)` (Def 3.1.3). -/
def nefSet (E : (ι → Prop) → Prop) (H : ι → HP) : Set ℝ² := {p | E fun i => (H i).mem p}

/-- Monotone boolean functions (Def 3.1.2). -/
def MonotoneBool (E : (ι → Prop) → Prop) : Prop := ∀ P Q : ι → Prop, (∀ i, P i → Q i) → E P → E Q

theorem measurableSet_nefSet [Finite ι] (E : (ι → Prop) → Prop) (H : ι → HP) :
    MeasurableSet (nefSet E H) := by
  classical
  have e : nefSet E H = ⋃ P : ι → Bool, ⋃ (_ : E fun i => P i = true),
      ⋂ i, {p : ℝ² | (H i).mem p ↔ P i = true} := by
    ext p
    simp only [nefSet, mem_ofPred_eq, mem_iUnion, mem_iInter]
    constructor
    · intro h
      refine ⟨fun i => decide ((H i).mem p), ?_, fun i => ?_⟩
      · convert h using 2 with i
        simp
      · simp
    · rintro ⟨P, hP, hp⟩
      convert hP using 2 with i
      exact hp i
  rw [e]
  refine MeasurableSet.iUnion fun P => MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun i => ?_
  cases P i
  · have : {p : ℝ² | (H i).mem p ↔ false = true} = {p | (H i).mem p}ᶜ := by
      ext p; simp
    rw [this]
    exact (H i).measurableSet_mem.compl
  · have : {p : ℝ² | (H i).mem p ↔ true = true} = {p | (H i).mem p} := by
      ext p; simp
    rw [this]
    exact (H i).measurableSet_mem

/-! ## Slices of Nef sets -/

lemma slice_nefSet_symmDiff_subset (E : (ι → Prop) → Prop) (H H' : ι → HP) (t s s' : ℝ) :
    slice (nefSet E H) t s ∆ slice (nefSet E H') t s' ⊆
      ⋃ j, {r : ℝ | ¬ ((H j).mem (s • u t + r • v t) ↔ (H' j).mem (s' • u t + r • v t))} := by
  intro r hr
  by_contra hcon
  simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_not] at hcon
  have heq : (fun i => (H i).mem (s • u t + r • v t)) =
      (fun i => (H' i).mem (s' • u t + r • v t)) := funext fun i => propext (hcon i)
  have key : r ∈ slice (nefSet E H) t s ↔ r ∈ slice (nefSet E H') t s' := by
    show E _ ↔ E _
    rw [heq]
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 (key.1 h1)
  · exact h2 (key.2 h1)

/-- The slices of two Nef sets with the same angles differ by at most the total
displacement of the (non-parallel) endpoints, provided the parallel half-planes agree. -/
theorem volume_slice_symmDiff_le [Fintype ι] (E : (ι → Prop) → Prop) (H H' : ι → HP)
    (hθ : ∀ j, (H j).θ = (H' j).θ) (t s s' : ℝ)
    (hpar : ∀ j, sin ((H j).θ - t) = 0 →
      ∀ r : ℝ, ((H j).mem (s • u t + r • v t) ↔ (H' j).mem (s' • u t + r • v t))) :
    volume (slice (nefSet E H) t s ∆ slice (nefSet E H') t s') ≤
      ∑ j, ENNReal.ofReal |(H j).endpt t s - (H' j).endpt t s'| := by
  refine (measure_mono (slice_nefSet_symmDiff_subset E H H' t s s')).trans ?_
  refine (measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  by_cases hsin : sin ((H j).θ - t) = 0
  · have : {r : ℝ | ¬((H j).mem (s • u t + r • v t) ↔ (H' j).mem (s' • u t + r • v t))} = ∅ := by
      ext r
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_not]
      exact hpar j hsin r
    rw [this, measure_empty]
    exact zero_le
  · calc volume {r : ℝ | ¬((H j).mem (s • u t + r • v t) ↔ (H' j).mem (s' • u t + r • v t))}
        ≤ volume (Icc (min ((H j).endpt t s) ((H' j).endpt t s'))
            (max ((H j).endpt t s) ((H' j).endpt t s'))) := by
          refine measure_mono fun r hr => ?_
          by_contra h
          exact hr (HP.mem_iff_of_not_mem_Icc (hθ j) hsin h)
      _ = ENNReal.ofReal |(H j).endpt t s - (H' j).endpt t s'| := by
          rw [Real.volume_Icc, max_sub_min_eq_abs, abs_sub_comm]

lemma abs_toReal_sub_le_of_symmDiff {A B : Set ℝ} (hA : volume A ≠ ⊤) (hB : volume B ≠ ⊤) :
    |(volume A).toReal - (volume B).toReal| ≤ (volume (A ∆ B)).toReal := by
  have hAB : volume (A ∆ B) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hA, hB⟩)
      ((measure_mono symmDiff_subset_union).trans (measure_union_le A B))
  have h1 : volume A ≤ volume B + volume (A ∆ B) :=
    (measure_mono (fun x hx => by
      by_cases hxB : x ∈ B
      · exact Or.inl hxB
      · exact Or.inr (Or.inl ⟨hx, hxB⟩))).trans (measure_union_le B (A ∆ B))
  have h2 : volume B ≤ volume A + volume (A ∆ B) :=
    (measure_mono (fun x hx => by
      by_cases hxA : x ∈ A
      · exact Or.inl hxA
      · exact Or.inr (Or.inr ⟨hx, hxA⟩))).trans (measure_union_le A (A ∆ B))
  have h1' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hB, hAB⟩) h1
  have h2' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hA, hAB⟩) h2
  rw [ENNReal.toReal_add hB hAB] at h1'
  rw [ENNReal.toReal_add hA hAB] at h2'
  rw [abs_le]
  constructor <;> linarith

/-- A boolean function that does not look at the input `i`. -/
def IgnoresIdx (E : (ι → Prop) → Prop) (i : ι) : Prop :=
  ∀ P Q : ι → Prop, (∀ j, j ≠ i → (P j ↔ Q j)) → (E P ↔ E Q)

lemma nefSet_update_of_ignores [DecidableEq ι] {E : (ι → Prop) → Prop} {i : ι}
    (hE : IgnoresIdx E i) (H : ι → HP) (G : HP) :
    nefSet E (Function.update H i G) = nefSet E H := by
  ext p
  refine hE _ _ fun j hj => ?_
  rw [Function.update_of_ne hj]

/-! ## Pushing one half-plane: the area derivative (replaces Thm 3.1.2) -/

section push

variable [DecidableEq ι]

/-- The defining half-planes with the `i`-th one pushed out by `δ`. -/
def pushed (H : ι → HP) (i : ι) (δ : ℝ) : ι → HP :=
  Function.update H i ((H i).withOffset ((H i).c + δ))

/-- `switchE E i P` holds iff switching the `i`-th input on changes `E` from false to true. -/
def switchE (E : (ι → Prop) → Prop) (i : ι) : (ι → Prop) → Prop :=
  fun P => E (Function.update P i True) ∧ ¬ E (Function.update P i False)

lemma switchE_ignores (E : (ι → Prop) → Prop) (i : ι) : IgnoresIdx (switchE E i) i := by
  intro P Q hPQ
  have h : ∀ b : Prop, Function.update P i b = Function.update Q i b := fun b => by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]; exact propext (hPQ j hj)
  simp only [switchE, h]

lemma pushed_apply_ne {H : ι → HP} {i j : ι} (hj : j ≠ i) (δ : ℝ) : pushed H i δ j = H j :=
  Function.update_of_ne hj _ _

lemma pushed_apply_self (H : ι → HP) (i : ι) (δ : ℝ) :
    pushed H i δ i = (H i).withOffset ((H i).c + δ) :=
  Function.update_self _ _ _

lemma mem_pushed_iff_of_ne {H : ι → HP} {i j : ι} (hj : j ≠ i) (δ : ℝ) (p : ℝ²) :
    (pushed H i δ j).mem p ↔ (H j).mem p := by rw [pushed_apply_ne hj]

/-- Rewriting the membership vector of `pushed` in terms of that of `H`. -/
lemma pushed_mems_eq {H : ι → HP} {i : ι} {δ : ℝ} {p : ℝ²} (b : Prop)
    (hb : (pushed H i δ i).mem p ↔ b) :
    (fun j => (pushed H i δ j).mem p) = Function.update (fun j => (H j).mem p) i b := by
  funext j
  by_cases hj : j = i
  · subst hj; simp only [Function.update_self]; exact propext hb
  · rw [Function.update_of_ne hj]; exact propext (mem_pushed_iff_of_ne hj δ p)

lemma mems_eq_update_self {H : ι → HP} {i : ι} {p : ℝ²} (b : Prop) (hb : (H i).mem p ↔ b) :
    (fun j => (H j).mem p) = Function.update (fun j => (H j).mem p) i b := by
  funext j
  by_cases hj : j = i
  · subst hj; simp only [Function.update_self]; exact propext hb
  · rw [Function.update_of_ne hj]

variable {E : (ι → Prop) → Prop} {H : ι → HP} {i : ι}

lemma nefSet_subset_pushed (hE : MonotoneBool E) {δ : ℝ} (hδ : 0 ≤ δ) :
    nefSet E H ⊆ nefSet E (pushed H i δ) := by
  intro p hp
  refine hE _ _ (fun j hj => ?_) hp
  by_cases hji : j = i
  · subst hji
    rw [pushed_apply_self]
    have : (H j).withOffset (H j).c = H j := rfl
    rw [← this] at hj
    exact HP.mem_mono _ (by linarith) hj
  · rwa [mem_pushed_iff_of_ne hji]

/-- Inside the open strip, the added region is exactly the switching set. -/
lemma mem_pushed_sdiff_iff {δ : ℝ} {p : ℝ²} (h1 : (H i).c < ⟪p, u (H i).θ⟫)
    (h2 : ⟪p, u (H i).θ⟫ < (H i).c + δ) :
    p ∈ nefSet E (pushed H i δ) \ nefSet E H ↔ p ∈ nefSet (switchE E i) H := by
  have hpu : (pushed H i δ i).mem p ↔ True := by
    rw [pushed_apply_self, iff_true]
    exact HP.mem_withOffset_of_inner h2
  have hH : (H i).mem p ↔ False := by
    rw [iff_false]; exact HP.not_mem_of_inner h1
  simp only [Set.mem_sdiff, nefSet, mem_ofPred_eq, switchE]
  rw [pushed_mems_eq True hpu, mems_eq_update_self False hH]
  simp only [Function.update_idem]

/-- Outside the closed strip, the added region is empty. -/
lemma not_mem_pushed_sdiff {δ : ℝ} (hδ : 0 ≤ δ) {p : ℝ²}
    (h : ⟪p, u (H i).θ⟫ < (H i).c ∨ (H i).c + δ < ⟪p, u (H i).θ⟫) :
    p ∉ nefSet E (pushed H i δ) \ nefSet E H := by
  rintro ⟨h1, h2⟩
  apply h2
  have key : (pushed H i δ i).mem p ↔ (H i).mem p := by
    rw [pushed_apply_self]
    rcases h with h | h
    · exact iff_of_true (HP.mem_withOffset_of_inner (by linarith)) (HP.mem_of_inner_lt h)
    · exact iff_of_false (HP.not_mem_of_inner (by simpa using h))
        (HP.not_mem_of_inner (by linarith))
  have heq : (fun j => (pushed H i δ j).mem p) = fun j => (H j).mem p := by
    funext j
    by_cases hj : j = i
    · subst hj; exact propext key
    · exact propext (mem_pushed_iff_of_ne hj δ p)
  show E _
  rw [← heq]
  exact h1

end push

/-! ## The area derivative -/

section deriv

variable [DecidableEq ι] {E : (ι → Prop) → Prop} {H : ι → HP} {i : ι}

lemma slice_pushed_sdiff_eq {δ s : ℝ} (hs : s ∈ Ioo (H i).c ((H i).c + δ)) :
    slice (nefSet E (pushed H i δ) \ nefSet E H) (H i).θ s =
      slice (nefSet (switchE E i) H) (H i).θ s := by
  ext r
  simp only [slice, mem_ofPred_eq]
  apply mem_pushed_sdiff_iff
  · rw [inner_add_smul_u_v]; exact hs.1
  · rw [inner_add_smul_u_v]; exact hs.2

lemma slice_pushed_sdiff_eq_empty {δ s : ℝ} (hδ : 0 ≤ δ)
    (hs : s ∉ Icc (H i).c ((H i).c + δ)) :
    slice (nefSet E (pushed H i δ) \ nefSet E H) (H i).θ s = ∅ := by
  ext r
  simp only [slice, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  apply not_mem_pushed_sdiff hδ
  rw [inner_add_smul_u_v]
  simp only [mem_Icc, not_and_or, not_le] at hs
  exact hs

/-- `|X_δ ∖ X| = ∫_{(c, c+δ)} |slice W|`. -/
lemma volume_pushed_sdiff [Finite ι] {δ : ℝ} (hδ : 0 ≤ δ) :
    volume (nefSet E (pushed H i δ) \ nefSet E H) =
      ∫⁻ s in Ioo (H i).c ((H i).c + δ), volume (slice (nefSet (switchE E i) H) (H i).θ s) := by
  have hmeas : MeasurableSet (nefSet E (pushed H i δ) \ nefSet E H) :=
    (measurableSet_nefSet _ _).diff (measurableSet_nefSet _ _)
  rw [volume_eq_lintegral_slice (H i).θ hmeas,
    ← setLIntegral_eq_of_support_subset (s := Icc (H i).c ((H i).c + δ))]
  · rw [setLIntegral_congr Ioo_ae_eq_Icc.symm]
    exact setLIntegral_congr_fun measurableSet_Ioo fun s hs => by rw [slice_pushed_sdiff_eq hs]
  · intro s hs
    by_contra h
    apply hs
    simp only [slice_pushed_sdiff_eq_empty hδ h, measure_empty]

lemma volume_slice_le {Y : Set ℝ²} {R : ℝ} (hY : ∀ p ∈ Y, ‖p‖ ≤ R) (t s : ℝ) :
    volume (slice Y t s) ≤ ENNReal.ofReal (2 * R) := by
  have hsub : slice Y t s ⊆ Icc (-R) R := by
    intro r hr
    have h := hY _ hr
    have h2 := abs_real_inner_le_norm (s • u t + r • v t) (v t)
    rw [inner_add_smul_v_v, norm_v, mul_one] at h2
    exact abs_le.1 (h2.trans h)
  refine (measure_mono hsub).trans (le_of_eq ?_)
  rw [Real.volume_Icc]
  congr 1
  ring

lemma slice_switch_subset {δ s : ℝ} (hs : s < (H i).c + δ) :
    slice (nefSet (switchE E i) H) (H i).θ s ⊆ slice (nefSet E (pushed H i δ)) (H i).θ s := by
  intro r hr
  obtain ⟨h1, -⟩ := hr
  show E _
  have hpu : (pushed H i δ i).mem (s • u (H i).θ + r • v (H i).θ) ↔ True := by
    rw [pushed_apply_self, iff_true]
    apply HP.mem_withOffset_of_inner
    rw [inner_add_smul_u_v]
    exact hs
  rw [pushed_mems_eq True hpu]
  exact h1

/-- A half-plane transversal to `l(θ, ·)` with a fixed slice endpoint. -/
def dummyHP (θ : ℝ) : HP := ⟨θ + π / 2, 0, false⟩

lemma measurable_volume_slice {Y : Set ℝ²} (hY : MeasurableSet Y) (t : ℝ) :
    Measurable fun s => volume (slice Y t s) :=
  measurable_measure_prodMk_left ((measurable_rotCoord t) hY)

lemma nefSet_pushed_mono (hE : MonotoneBool E) {δ δ' : ℝ} (h : δ ≤ δ') :
    nefSet E (pushed H i δ) ⊆ nefSet E (pushed H i δ') := by
  intro p hp
  refine hE _ _ (fun j hj => ?_) hp
  by_cases hji : j = i
  · subst hji
    rw [pushed_apply_self] at hj ⊢
    exact HP.mem_mono _ (by linarith) hj
  · rwa [mem_pushed_iff_of_ne hji] at hj ⊢

lemma pushed_zero_eq (H : ι → HP) (i : ι) : nefSet E (pushed H i 0) = nefSet E H := by
  have : pushed H i 0 = H := by
    funext j
    by_cases hj : j = i
    · subst hj; rw [pushed_apply_self, add_zero]; rfl
    · exact pushed_apply_ne hj 0
  rw [this]

/-- **Area derivative.**  Pushing the `i`-th defining half-plane of a simple Nef set with
monotone `E` outwards by `δ` changes the area at the rate `|slice W|` at `δ = 0⁺`, where `W` is
the switching set along the line `l_i`. -/
theorem hasDerivWithinAt_volume_pushed [Fintype ι] (hE : MonotoneBool E)
    (hsimple : ∀ j, j ≠ i → sin ((H j).θ - (H i).θ) = 0 →
      (H i).c * cos ((H j).θ - (H i).θ) ≠ (H j).c)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hbdd : Bornology.IsBounded (nefSet E (pushed H i δ₀))) :
    HasDerivWithinAt (fun δ => (volume (nefSet E (pushed H i δ))).toReal)
      (volume (slice (nefSet (switchE E i) H) (H i).θ (H i).c)).toReal (Ici 0) 0 := by
  classical
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hbdd
  have hWm : MeasurableSet (nefSet (switchE E i) H) := measurableSet_nefSet _ _
  set φ : ℝ → ℝ := fun s => (volume (slice (nefSet (switchE E i) H) (H i).θ s)).toReal with hφ
  have hle : ∀ s, s < (H i).c + δ₀ →
      volume (slice (nefSet (switchE E i) H) (H i).θ s) ≤ ENNReal.ofReal (2 * R) := fun s hs =>
    (measure_mono (slice_switch_subset hs)).trans (volume_slice_le hR _ _)
  have hfin : ∀ s, s < (H i).c + δ₀ →
      volume (slice (nefSet (switchE E i) H) (H i).θ s) ≠ ⊤ := fun s hs =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle s hs)
  have hbound : ∀ s, s < (H i).c + δ₀ → φ s ≤ max (2 * R) 0 := fun s hs => by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hle s hs)
    rwa [ENNReal.toReal_ofReal'] at this
  have hφm : Measurable φ := (measurable_volume_slice hWm _).ennreal_toReal
  -- the dummy representation of `W`
  set H₁ := Function.update H i (dummyHP (H i).θ) with hH₁
  have hW₁ : nefSet (switchE E i) H₁ = nefSet (switchE E i) H :=
    nefSet_update_of_ignores (switchE_ignores E i) H _
  -- a safety margin for the parallel half-planes
  obtain ⟨η, hη, hηle⟩ : ∃ η > 0, ∀ j, j ≠ i → sin ((H j).θ - (H i).θ) = 0 →
      η ≤ |(H i).c * cos ((H j).θ - (H i).θ) - (H j).c| := by
    let g : ι → ℝ := fun j => if j ≠ i ∧ sin ((H j).θ - (H i).θ) = 0 then
      |(H i).c * cos ((H j).θ - (H i).θ) - (H j).c| else 1
    have hne : (Finset.univ : Finset ι).Nonempty := ⟨i, Finset.mem_univ i⟩
    refine ⟨Finset.univ.inf' hne g, ?_, fun j hj hs => ?_⟩
    · show 0 < _
      rw [Finset.lt_inf'_iff]
      intro j _
      simp only [g]
      split_ifs with h
      · exact abs_pos.2 (sub_ne_zero.2 (hsimple j h.1 h.2))
      · exact one_pos
    · have := Finset.inf'_le g (Finset.mem_univ j)
      have hg : g j = |(H i).c * cos ((H j).θ - (H i).θ) - (H j).c| := if_pos ⟨hj, hs⟩
      rw [hg] at this
      exact this
  -- the Lipschitz constant
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = ∑ j, |cos ((H₁ j).θ - (H i).θ) / sin ((H₁ j).θ - (H i).θ)| :=
    ⟨_, rfl⟩
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; exact Finset.sum_nonneg fun j _ => abs_nonneg _
  have hlip : ∀ s, (H i).c ≤ s → s < (H i).c + min η δ₀ →
      |φ s - φ (H i).c| ≤ Λ * (s - (H i).c) := by
    intro s hs1 hs2
    have hsη : s - (H i).c < η := by linarith [min_le_left η δ₀]
    have hsδ : s < (H i).c + δ₀ := by linarith [min_le_right η δ₀]
    have hcδ : (H i).c < (H i).c + δ₀ := by linarith
    refine (abs_toReal_sub_le_of_symmDiff (hfin s hsδ) (hfin _ hcδ)).trans ?_
    have hpar : ∀ j, sin ((H₁ j).θ - (H i).θ) = 0 → ∀ r : ℝ,
        ((H₁ j).mem (s • u (H i).θ + r • v (H i).θ) ↔
          (H₁ j).mem ((H i).c • u (H i).θ + r • v (H i).θ)) := by
      intro j hsin r
      by_cases hj : j = i
      · exfalso
        subst hj
        rw [hH₁, Function.update_self] at hsin
        simp only [dummyHP, add_sub_cancel_left, sin_pi_div_two] at hsin
        exact one_ne_zero hsin
      · have hHj : H₁ j = H j := Function.update_of_ne hj _ _
        rw [hHj] at hsin ⊢
        have ha := hηle j hj hsin
        have e1 : ⟪s • u (H i).θ + r • v (H i).θ, u (H j).θ⟫ =
            s * cos ((H j).θ - (H i).θ) := by rw [inner_rotCoord_u, hsin]; ring
        have e2 : ⟪(H i).c • u (H i).θ + r • v (H i).θ, u (H j).θ⟫ =
            (H i).c * cos ((H j).θ - (H i).θ) := by rw [inner_rotCoord_u, hsin]; ring
        have hcos : |cos ((H j).θ - (H i).θ)| ≤ 1 := abs_cos_le_one _
        have hdiff : |s * cos ((H j).θ - (H i).θ) - (H i).c * cos ((H j).θ - (H i).θ)| < η := by
          rw [← sub_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ s - (H i).c)]
          calc (s - (H i).c) * |cos ((H j).θ - (H i).θ)| ≤ (s - (H i).c) * 1 :=
                mul_le_mul_of_nonneg_left hcos (by linarith)
            _ < η := by linarith
        rw [abs_sub_lt_iff] at hdiff
        rcases lt_or_gt_of_ne (sub_ne_zero.2 (hsimple j hj hsin)) with hneg | hpos
        · rw [abs_of_neg hneg] at ha
          exact iff_of_true (HP.mem_of_inner_lt (by rw [e1]; linarith))
            (HP.mem_of_inner_lt (by rw [e2]; linarith))
        · rw [abs_of_pos hpos] at ha
          exact iff_of_false (HP.not_mem_of_inner (by rw [e1]; linarith))
            (HP.not_mem_of_inner (by rw [e2]; linarith))
    have key := volume_slice_symmDiff_le (switchE E i) H₁ H₁ (fun _ => rfl)
      (H i).θ s (H i).c hpar
    rw [hW₁] at key
    have hsum : ∑ j, ENNReal.ofReal |(H₁ j).endpt (H i).θ s - (H₁ j).endpt (H i).θ (H i).c| =
        ENNReal.ofReal (Λ * (s - (H i).c)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => abs_nonneg _), hΛ, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [HP.endpt, HP.endpt, div_sub_div_same,
        show (H₁ j).c - s * cos ((H₁ j).θ - (H i).θ) -
          ((H₁ j).c - (H i).c * cos ((H₁ j).θ - (H i).θ)) =
          ((H i).c - s) * cos ((H₁ j).θ - (H i).θ) by ring,
        mul_div_assoc, abs_mul, abs_of_nonpos (by linarith : (H i).c - s ≤ 0)]
      ring
    rw [hsum] at key
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hΛ0 (by linarith)) key
  -- right-continuity of `φ` at `c`
  have hcont : ContinuousWithinAt φ (Ioi (H i).c) (H i).c := by
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hΛ1 : 0 < Λ + 1 := by linarith
    refine ⟨min (min η δ₀) (ε / (Λ + 1)), lt_min (lt_min hη hδ₀) (div_pos hε hΛ1),
      fun {s} hs hsd => ?_⟩
    have hs' : (H i).c ≤ s := le_of_lt hs
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hs')] at hsd
    rw [Real.dist_eq]
    have h1 := hlip s hs' (by linarith [min_le_left (min η δ₀) (ε / (Λ + 1))])
    have h2 : s - (H i).c < ε / (Λ + 1) := lt_of_lt_of_le hsd (min_le_right _ _)
    calc |φ s - φ (H i).c| ≤ Λ * (s - (H i).c) := h1
      _ ≤ Λ * (ε / (Λ + 1)) := mul_le_mul_of_nonneg_left h2.le hΛ0
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ hΛ1]
        nlinarith
  -- integrability of `φ` near `c`
  have hint : ∀ b, (H i).c ≤ b → b < (H i).c + δ₀ → IntervalIntegrable φ volume (H i).c b := by
    intro b hb1 hb2
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb1]
    refine Measure.integrableOn_of_bounded (M := max (2 * R) 0) measure_Ioc_lt_top.ne
      hφm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact hbound s (by linarith [hs.2])
  -- the volume identity
  have hX : ∀ δ, 0 ≤ δ → δ < δ₀ → (volume (nefSet E (pushed H i δ))).toReal =
      (volume (nefSet E H)).toReal + ∫ s in (H i).c..((H i).c + δ), φ s := by
    intro δ hδ hδ'
    have hsub := nefSet_subset_pushed (E := E) (H := H) (i := i) hE hδ
    have hXfin : volume (nefSet E (pushed H i δ)) ≠ ⊤ :=
      ne_top_of_le_ne_top hbdd.measure_lt_top.ne (measure_mono (nefSet_pushed_mono hE hδ'.le))
    have hX0fin : volume (nefSet E H) ≠ ⊤ := ne_top_of_le_ne_top hXfin (measure_mono hsub)
    have e1 := measure_add_sdiff (μ := volume) (measurableSet_nefSet E H).nullMeasurableSet
      (nefSet E (pushed H i δ))
    rw [union_eq_self_of_subset_left hsub] at e1
    have e2 := volume_pushed_sdiff (E := E) (H := H) (i := i) hδ
    have e3 : ∫⁻ s in Ioo (H i).c ((H i).c + δ),
        volume (slice (nefSet (switchE E i) H) (H i).θ s) =
        ∫⁻ s in Ioo (H i).c ((H i).c + δ), ENNReal.ofReal (φ s) :=
      setLIntegral_congr_fun measurableSet_Ioo fun s hs =>
        (ENNReal.ofReal_toReal (hfin s (by linarith [hs.2]))).symm
    have hintO : IntegrableOn φ (Ioo (H i).c ((H i).c + δ)) := by
      have := (hint ((H i).c + δ) (by linarith) (by linarith)).1
      exact this.mono_set Ioo_subset_Ioc_self
    have e4 := ofReal_integral_eq_lintegral_ofReal hintO
      (Eventually.of_forall fun s => ENNReal.toReal_nonneg)
    rw [← e1, e2, e3, ← e4, ENNReal.toReal_add hX0fin ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioo fun s _ => ENNReal.toReal_nonneg),
      intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  -- FTC
  have hftc : HasDerivWithinAt (fun b => ∫ s in (H i).c..b, φ s) (φ (H i).c)
      (Ici (H i).c) (H i).c :=
    intervalIntegral.integral_hasDerivWithinAt_right (hint _ le_rfl (by linarith))
      hφm.stronglyMeasurable.stronglyMeasurableAtFilter hcont
  have htrans : HasDerivWithinAt (fun δ : ℝ => (H i).c + δ) 1 (Ici 0) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_add (H i).c).hasDerivWithinAt
  have hcomp : HasDerivWithinAt (fun δ => ∫ s in (H i).c..((H i).c + δ), φ s) (φ (H i).c * 1)
      (Ici 0) 0 := by
    have hftc' : HasDerivWithinAt (fun b => ∫ s in (H i).c..b, φ s) (φ (H i).c)
        (Ici (H i).c) ((H i).c + 0) := by rw [add_zero]; exact hftc
    exact hftc'.comp 0 htrans fun δ hδ => by
      simp only [mem_Ici] at hδ ⊢; linarith
  rw [mul_one] at hcomp
  have hfinal := hcomp.const_add (volume (nefSet E H)).toReal
  refine hfinal.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [Ico_mem_nhdsGE hδ₀] with δ hδ
    exact hX δ hδ.1 hδ.2
  · rw [hX 0 le_rfl hδ₀, add_zero]

end deriv

end Sofa
