/-
# Hammersley's upper bound for the moving sofa problem  —  `sofaConstant ≤ 2√2`

Target environment
  * Lean 4.33.1 / Mathlib tag `v4.33.1`
    (exactly what `google-deepmind/formal-conjectures` pins on 2026-09-16, commit 40e7c98).
  * Definitions of `horizontalHallway`, `verticalHallway`, `hallway`, `E(2)`, `IsMovingSofa`,
    `sofaConstant` are copied VERBATIM from
    `FormalConjectures/Wikipedia/MovingSofa.lean` (upstream main, 2026-09-16) so that the
    theorem below is literally about the upstream `sofaConstant`.

PROOF STATUS  (please read before trusting anything)
  * MATHEMATICS: complete, elementary, classical (Hammersley 1968).  A full natural-language
    proof is in the accompanying report; the Lean text follows it step by step.
  * LEAN CHECKING: [PROOF-C] [AXIOM-CHECK] — compiled 2026-09-16 on the user's machine
    (Lean 4.33.1 / Mathlib v4.33.1, `lake build` clean, no `sorry`), and
      #print axioms MovingSofa.sofaConstant_le_two_mul_sqrt_two
        → [propext, Classical.choice, Quot.sound]
      #print axioms MovingSofa.sofaConstant_ne_top
        → [propext, Classical.choice, Quot.sound]
    (Round 1 had two local errors, fixed in round 2; the project file `Sofa/Hammersley.lean`
    is this file.)
  * This file contains NO `sorry` (in code).  Baek's optimality theorem is only *discussed* in
    a comment at the end; its formal statement already lives upstream as
    `MovingSofa.sofaConstant_eq_volume_gerversSofa` (with `sorry`).

How to compile
  1. Inside a Mathlib project at tag v4.33.1: `lake env lean MovingSofaHammersley.lean`.
  2. Inside `formal-conjectures`: delete the block marked `-- BEGIN upstream copy … -- END`
     and the `local notation "ℝ²"` line, and `import FormalConjecturesUtil` instead.
-/
import SofaSubmission.Defs

noncomputable section

open MeasureTheory Topology
open scoped Real unitInterval ENNReal

open scoped EuclideanGeometry

namespace MovingSofa

-- (upstream definitions come from `Sofa.Upstream`)

/-! ## Coordinates of hallway membership -/

lemma mem_horizontalHallway_iff (p : ℝ²) :
    p ∈ horizontalHallway ↔ p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 := by
  constructor
  · rintro ⟨x, y, h, rfl⟩
    exact h
  · intro h
    exact ⟨p 0, p 1, h, by ext i; fin_cases i <;> rfl⟩

lemma mem_verticalHallway_iff (p : ℝ²) :
    p ∈ verticalHallway ↔ 0 ≤ p 0 ∧ p 0 ≤ 1 ∧ p 1 ≤ 1 := by
  constructor
  · rintro ⟨x, y, h, rfl⟩
    exact h
  · intro h
    exact ⟨p 0, p 1, h, by ext i; fin_cases i <;> rfl⟩

/-! ## Rigid motions in coordinates

For `g : E(2)` write `g q = L q + g 0` with `L = g.linearIsometryEquiv`.  Since `L` is linear,
`(L q) i = (L e₀) i * q 0 + (L e₁) i * q 1`, and since `L` is an isometry,
`(L e₀) 0 ^ 2 + (L e₀) 1 ^ 2 = 1` — i.e. `(L e₀) = (cos θ, sin θ)` for the rotation angle `θ`
(or its mirror image; the argument never needs orientation). -/

/-- The first standard basis vector `(1, 0)`. -/
def e₀ : ℝ² := !₂[1, 0]

/-- The second standard basis vector `(0, 1)`. -/
def e₁ : ℝ² := !₂[0, 1]

lemma apply_eq_linear_add (g : E(2)) (q : ℝ²) :
    g q = g.linearIsometryEquiv q + g 0 := by
  have h := g.map_vadd (0 : ℝ²) q
  simp only [vadd_eq_add, add_zero] at h
  exact h

lemma decomp_e (q : ℝ²) : q = q 0 • e₀ + q 1 • e₁ := by
  ext i
  fin_cases i <;> simp [e₀, e₁]

lemma linearIsometryEquiv_apply_coord (L : ℝ² ≃ₗᵢ[ℝ] ℝ²) (q : ℝ²) (i : Fin 2) :
    (L q) i = (L e₀) i * q 0 + (L e₁) i * q 1 := by
  conv_lhs => rw [decomp_e q]
  simp only [map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma apply_coord (g : E(2)) (q : ℝ²) (i : Fin 2) :
    (g q) i = (g.linearIsometryEquiv e₀) i * q 0 + (g.linearIsometryEquiv e₁) i * q 1
      + (g 0) i := by
  rw [apply_eq_linear_add g q, PiLp.add_apply, linearIsometryEquiv_apply_coord]

/-- `cos² + sin² = 1`: the image of `e₀` under a linear isometry is a unit vector. -/
lemma sq_add_sq_eq_one (L : ℝ² ≃ₗᵢ[ℝ] ℝ²) : (L e₀) 0 ^ 2 + (L e₀) 1 ^ 2 = 1 := by
  have h1 := EuclideanSpace.real_norm_sq_eq (L e₀)
  have h2 := EuclideanSpace.real_norm_sq_eq e₀
  rw [Fin.sum_univ_two] at h1 h2
  rw [L.norm_map] at h1
  have h3 : e₀ 0 ^ 2 + e₀ 1 ^ 2 = 1 := by simp [e₀, PiLp.toLp_apply]
  linarith

/-! ## Continuity along the motion -/

/-- Evaluation at a fixed point is continuous for the (induced) topology on `E(2)`. -/
lemma continuous_eval (q : ℝ²) : Continuous fun g : E(2) => g q := by
  have hF : Continuous fun g : E(2) => g.toAffineIsometry.toContinuousAffineMap := by
    exact continuous_induced_dom
  have hD := (ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ ℝ² ℝ²).continuous
  have h1 : Continuous fun g : E(2) =>
      (ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ ℝ² ℝ²
        g.toAffineIsometry.toContinuousAffineMap).1 :=
    continuous_fst.comp (hD.comp hF)
  have h2 : Continuous fun g : E(2) =>
      (ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ ℝ² ℝ²
        g.toAffineIsometry.toContinuousAffineMap).2 :=
    continuous_snd.comp (hD.comp hF)
  have key : ∀ f : ℝ² →ᴬ[ℝ] ℝ²,
      f q = (ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ ℝ² ℝ² f).2 q
        + (ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ ℝ² ℝ² f).1 := by
    intro f
    have h := ContinuousAffineMap.decompLinearIsometryEquiv_symm_apply ℝ ℝ ℝ² ℝ²
      (ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ ℝ² ℝ² f) q
    rwa [LinearIsometryEquiv.symm_apply_apply] at h
  have heq : (fun g : E(2) => g q) = fun g : E(2) =>
      (ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ ℝ² ℝ²
        g.toAffineIsometry.toContinuousAffineMap).2 q
      + (ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ ℝ² ℝ²
        g.toAffineIsometry.toContinuousAffineMap).1 := by
    funext g
    have h := key g.toAffineIsometry.toContinuousAffineMap
    exact h
  rw [heq]
  exact (h2.clm_apply continuous_const).add h1

/-- Along a continuous motion, the coordinates of the linear part are continuous in time. -/
lemma continuous_linear_coord {m : I → E(2)} (hm : Continuous m) (v : ℝ²) (i : Fin 2) :
    Continuous fun t => ((m t).linearIsometryEquiv v) i := by
  have h1 : Continuous fun t => m t v := (continuous_eval v).comp hm
  have h2 : Continuous fun t => m t 0 := (continuous_eval 0).comp hm
  have heq : (fun t => ((m t).linearIsometryEquiv v) i) =
      fun t => (m t v) i - (m t 0) i := by
    funext t
    rw [apply_eq_linear_add (m t) v, PiLp.add_apply]
    ring
  rw [heq]
  fun_prop

/-! ## The area of a parallelogram cut out of the unit horizontal strip -/

/-- The closed parallelogram `{(x, y) : 0 ≤ y ≤ 1, a ≤ n₁ x + n₂ y ≤ a + 1}` in `ℝ × ℝ`:
the intersection of the horizontal unit strip with a unit-width strip of normal `(n₁, n₂)`. -/
def para (n₁ n₂ a : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ 1 ∧ a ≤ n₁ * p.1 + n₂ * p.2 ∧ n₁ * p.1 + n₂ * p.2 ≤ a + 1}

lemma isClosed_para (n₁ n₂ a : ℝ) : IsClosed (para n₁ n₂ a) := by
  have hf : Continuous fun p : ℝ × ℝ => n₁ * p.1 + n₂ * p.2 :=
    (continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd)
  unfold para
  simp only [Set.ofPred_and]
  exact (isClosed_le continuous_const continuous_snd).inter
    ((isClosed_le continuous_snd continuous_const).inter
      ((isClosed_le continuous_const hf).inter (isClosed_le hf continuous_const)))

/-- Fubini: every horizontal slice of `para n₁ n₂ a` at height `y ∈ [0,1]` is an interval of
length `1 / n₁`, so the area is at most `1 / n₁` (in fact equal, but `≤` is all we need). -/
lemma volume_para_le (n₁ n₂ a : ℝ) (hn : 0 < n₁) :
    volume (para n₁ n₂ a) ≤ ENNReal.ofReal (1 / n₁) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm (isClosed_para n₁ n₂ a).measurableSet]
  calc ∫⁻ y, volume ((fun x => (x, y)) ⁻¹' para n₁ n₂ a)
      ≤ ∫⁻ y, (Set.Icc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (1 / n₁)) y := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ Set.Icc (0 : ℝ) 1
        · rw [Set.indicator_of_mem hy]
          calc volume ((fun x => (x, y)) ⁻¹' para n₁ n₂ a)
              ≤ volume (Set.Icc ((a - n₂ * y) / n₁) ((a + 1 - n₂ * y) / n₁)) := by
                apply measure_mono
                intro x hx
                simp only [para, Set.mem_preimage, Set.mem_ofPred_eq] at hx
                obtain ⟨-, -, h1, h2⟩ := hx
                rw [Set.mem_Icc]
                constructor
                · rw [div_le_iff₀ hn]; linarith
                · rw [le_div_iff₀ hn]; linarith
            _ = ENNReal.ofReal (1 / n₁) := by
                rw [Real.volume_Icc, ← sub_div]
                congr 1
                ring
        · have hempty : (fun x => (x, y)) ⁻¹' para n₁ n₂ a = ∅ := by
            apply Set.eq_empty_of_forall_notMem
            intro x hx
            simp only [para, Set.mem_preimage, Set.mem_ofPred_eq] at hx
            exact hy ⟨hx.1, hx.2.1⟩
          calc volume ((fun x => (x, y)) ⁻¹' para n₁ n₂ a) = 0 := by
                rw [hempty, measure_empty]
            _ ≤ (Set.Icc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (1 / n₁)) y :=
                zero_le
    _ = ENNReal.ofReal (1 / n₁) := by
        rw [lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc]
        simp

/-- Transport to `ℝ² = EuclideanSpace ℝ (Fin 2)`: if every point `q` of `S` satisfies
`0 ≤ q 1 ≤ 1` and `a ≤ n₁ q₀ + n₂ q₁ ≤ a + 1` with `n₁ > 0`, then `volume S ≤ 1 / n₁`. -/
lemma volume_le_of_forall_mem_para (S : Set ℝ²) (n₁ n₂ a : ℝ) (hn : 0 < n₁)
    (h : ∀ q ∈ S, a ≤ n₁ * q 0 + n₂ * q 1 ∧ n₁ * q 0 + n₂ * q 1 ≤ a + 1)
    (hS : ∀ q ∈ S, 0 ≤ q 1 ∧ q 1 ≤ 1) :
    volume S ≤ ENNReal.ofReal (1 / n₁) := by
  calc volume S
      ≤ volume ((WithLp.ofLp : ℝ² → (Fin 2 → ℝ)) ⁻¹'
          (MeasurableEquiv.finTwoArrow ⁻¹' para n₁ n₂ a)) := by
        apply measure_mono
        intro q hq
        have h1 := hS q hq
        have h2 := h q hq
        show MeasurableEquiv.finTwoArrow (WithLp.ofLp q) ∈ para n₁ n₂ a
        exact ⟨h1.1, h1.2, h2.1, h2.2⟩
    _ ≤ volume (MeasurableEquiv.finTwoArrow ⁻¹' para n₁ n₂ a) :=
        (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage_le _
    _ ≤ volume (para n₁ n₂ a) :=
        (volume_preserving_finTwoArrow ℝ).measure_preimage_le _
    _ ≤ ENNReal.ofReal (1 / n₁) := volume_para_le n₁ n₂ a hn

/-- Same as above with `n₁ ≠ 0` (flip the sign of the strip when `n₁ < 0`). -/
lemma volume_le_of_forall_mem_strip (S : Set ℝ²) (n₁ n₂ a : ℝ) (hn : n₁ ≠ 0)
    (h : ∀ q ∈ S, a ≤ n₁ * q 0 + n₂ * q 1 ∧ n₁ * q 0 + n₂ * q 1 ≤ a + 1)
    (hS : ∀ q ∈ S, 0 ≤ q 1 ∧ q 1 ≤ 1) :
    volume S ≤ ENNReal.ofReal (1 / |n₁|) := by
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have key := volume_le_of_forall_mem_para S (-n₁) (-n₂) (-(a + 1)) (by linarith)
      (fun q hq => by
        obtain ⟨h1, h2⟩ := h q hq
        refine ⟨?_, ?_⟩ <;> simp only [neg_mul] <;> linarith) hS
    rwa [abs_of_neg hneg]
  · have key := volume_le_of_forall_mem_para S n₁ n₂ a hpos h hS
    rwa [abs_of_pos hpos]

/-! ## Hammersley's bound -/

/-- **Hammersley (1968).**  Every moving sofa has area at most `2√2`.

Proof sketch (in the sofa's own frame, `L t := (m t).linearIsometryEquiv`,
`cos t := (L t e₀) 0`, `sin t := (L t e₀) 1`):
* `s` lies in the horizontal unit strip `{0 ≤ y ≤ 1}` (initial position);
* if `|cos 1| ≥ 1/√2`, the final position puts `s` inside a unit strip whose normal has
  first coordinate `cos 1`, so `s` sits in a parallelogram of area `1/|cos 1| ≤ √2`;
* otherwise `cos` (continuous, `cos 0 = 1`) takes the value `1/√2` at some time `t`
  (intermediate value theorem); then `|sin t| = 1/√2` as well, and at time `t` the sofa sits
  in the union of two parallelograms (one per hallway arm), each of area `√2`. -/
theorem volume_le_of_isMovingSofa {s : Set ℝ²} {m : I → E(2)} (hm : IsMovingSofa s m) :
    volume s ≤ ENNReal.ofReal (2 * Real.sqrt 2) := by
  set r : ℝ := Real.sqrt 2
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr1 : 1 ≤ r := by nlinarith [hr2, hr0]
  have hκ : 0 < 1 / r := one_div_pos.mpr hr0
  -- the sofa lies in the horizontal unit strip
  have hS : ∀ q ∈ s, 0 ≤ q 1 ∧ q 1 ≤ 1 := fun q hq =>
    ((mem_horizontalHallway_iff q).1 (hm.initial hq)).2
  -- `cos t := ((m t).linearIsometryEquiv e₀) 0` is continuous with `cos 0 = 1`
  have hc : Continuous fun t : I => ((m t).linearIsometryEquiv e₀) 0 :=
    continuous_linear_coord hm.continuous e₀ 0
  have hc0 : ((m 0).linearIsometryEquiv e₀) 0 = 1 := by
    have h : ((m 0).linearIsometryEquiv e₀) 0 = (m 0 e₀) 0 - (m 0 0) 0 := by
      rw [apply_eq_linear_add (m 0) e₀, PiLp.add_apply]
      ring
    rw [h, hm.zero]
    show e₀ 0 - (0 : ℝ²) 0 = 1
    simp [e₀, PiLp.toLp_apply]
  -- `cos² + sin² = 1`
  have hsq : ∀ t : I, ((m t).linearIsometryEquiv e₀) 0 ^ 2
      + ((m t).linearIsometryEquiv e₀) 1 ^ 2 = 1 :=
    fun t => sq_add_sq_eq_one (m t).linearIsometryEquiv
  by_cases hA : 1 / r ≤ |((m 1).linearIsometryEquiv e₀) 0|
  · -- Case A: the total rotation is at most 45° — use the final vertical strip.
    have hne : ((m 1).linearIsometryEquiv e₀) 0 ≠ 0 :=
      abs_pos.mp (lt_of_lt_of_le hκ hA)
    have hfin : ∀ q ∈ s, 0 ≤ (m 1 q) 0 ∧ (m 1 q) 0 ≤ 1 := fun q hq => by
      have h := (mem_verticalHallway_iff (m 1 q)).1 (hm.final ⟨q, hq, rfl⟩)
      exact ⟨h.1, h.2.1⟩
    have hvol := volume_le_of_forall_mem_strip s (((m 1).linearIsometryEquiv e₀) 0)
      (((m 1).linearIsometryEquiv e₁) 0) (-(m 1 0) 0) hne
      (fun q hq => by
        have h := apply_coord (m 1) q 0
        obtain ⟨h0, h1⟩ := hfin q hq
        constructor <;> linarith) hS
    calc volume s ≤ ENNReal.ofReal (1 / |((m 1).linearIsometryEquiv e₀) 0|) := hvol
      _ ≤ ENNReal.ofReal (2 * r) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : 1 / |((m 1).linearIsometryEquiv e₀) 0| ≤ 1 / (1 / r) :=
          one_div_le_one_div_of_le hκ hA
        rw [one_div_one_div] at h1
        linarith
  · -- Case B: the rotation passes through 45°.
    rw [not_le] at hA
    have hlt : ((m 1).linearIsometryEquiv e₀) 0 < 1 / r :=
      lt_of_le_of_lt (le_abs_self _) hA
    have hle : 1 / r ≤ ((m 0).linearIsometryEquiv e₀) 0 := by
      rw [hc0]; exact div_le_one_of_le₀ hr1 hr0.le
    -- intermediate value theorem on the connected space `I`
    obtain ⟨t, ht⟩ : ∃ t : I, ((m t).linearIsometryEquiv e₀) 0 = 1 / r :=
      intermediate_value_univ 1 0 hc ⟨hlt.le, hle⟩
    -- at time `t`: `cos t = 1/√2` and `|sin t| = 1/√2`
    have h12 : (1 / r) ^ 2 = 1 / 2 := by rw [div_pow, hr2]; norm_num
    have hsn : ((m t).linearIsometryEquiv e₀) 1 ^ 2 = (1 / r) ^ 2 := by
      have h := hsq t
      rw [ht, h12] at h
      rw [h12]; linarith
    have habs : |((m t).linearIsometryEquiv e₀) 1| = 1 / r := by
      rw [(sq_eq_sq_iff_abs_eq_abs _ _).1 hsn]
      exact abs_of_pos hκ
    have hcabs : |((m t).linearIsometryEquiv e₀) 0| = 1 / r := by
      rw [ht]; exact abs_of_pos hκ
    -- the two arms of the hallway at time `t`:
    --   A := {q ∈ s | m t q lies in the horizontal unit strip}
    --   B := {q ∈ s | m t q lies in the vertical unit strip}
    have hcover : s ⊆ {q ∈ s | 0 ≤ (m t q) 1 ∧ (m t q) 1 ≤ 1}
        ∪ {q ∈ s | 0 ≤ (m t q) 0 ∧ (m t q) 0 ≤ 1} := by
      intro q hq
      have h : m t q ∈ horizontalHallway ∪ verticalHallway := hm.subset_hallway t ⟨q, hq, rfl⟩
      rcases h with h | h
      · exact Or.inl ⟨hq, ((mem_horizontalHallway_iff _).1 h).2⟩
      · have h' := (mem_verticalHallway_iff _).1 h
        exact Or.inr ⟨hq, h'.1, h'.2.1⟩
    -- the horizontal arm: a parallelogram of area `1/|sin t| = √2`
    have hA_le : volume {q ∈ s | 0 ≤ (m t q) 1 ∧ (m t q) 1 ≤ 1} ≤ ENNReal.ofReal r := by
      have hne : ((m t).linearIsometryEquiv e₀) 1 ≠ 0 :=
        abs_pos.mp (by rw [habs]; exact hκ)
      have key := volume_le_of_forall_mem_strip {q ∈ s | 0 ≤ (m t q) 1 ∧ (m t q) 1 ≤ 1}
        (((m t).linearIsometryEquiv e₀) 1) (((m t).linearIsometryEquiv e₁) 1) (-(m t 0) 1) hne
        (fun q hq => by
          have h := apply_coord (m t) q 1
          obtain ⟨-, h0, h1⟩ := hq
          constructor <;> linarith)
        (fun q hq => hS q hq.1)
      rwa [habs, one_div_one_div] at key
    -- the vertical arm: a parallelogram of area `1/|cos t| = √2`
    have hB_le : volume {q ∈ s | 0 ≤ (m t q) 0 ∧ (m t q) 0 ≤ 1} ≤ ENNReal.ofReal r := by
      have hne : ((m t).linearIsometryEquiv e₀) 0 ≠ 0 :=
        abs_pos.mp (by rw [hcabs]; exact hκ)
      have key := volume_le_of_forall_mem_strip {q ∈ s | 0 ≤ (m t q) 0 ∧ (m t q) 0 ≤ 1}
        (((m t).linearIsometryEquiv e₀) 0) (((m t).linearIsometryEquiv e₁) 0) (-(m t 0) 0) hne
        (fun q hq => by
          have h := apply_coord (m t) q 0
          obtain ⟨-, h0, h1⟩ := hq
          constructor <;> linarith)
        (fun q hq => hS q hq.1)
      rwa [hcabs, one_div_one_div] at key
    calc volume s
        ≤ volume ({q ∈ s | 0 ≤ (m t q) 1 ∧ (m t q) 1 ≤ 1}
            ∪ {q ∈ s | 0 ≤ (m t q) 0 ∧ (m t q) 0 ≤ 1}) := measure_mono hcover
      _ ≤ volume {q ∈ s | 0 ≤ (m t q) 1 ∧ (m t q) 1 ≤ 1}
            + volume {q ∈ s | 0 ≤ (m t q) 0 ∧ (m t q) 0 ≤ 1} := measure_union_le _ _
      _ ≤ ENNReal.ofReal r + ENNReal.ofReal r := add_le_add hA_le hB_le
      _ = ENNReal.ofReal (2 * r) := by
        rw [← ENNReal.ofReal_add hr0.le hr0.le]
        congr 1
        ring

/-- **Hammersley's upper bound**: the sofa constant is at most `2√2 ≈ 2.8284`.
(Compare: Gerver's sofa has area `≈ 2.2195`, and Kallus–Romik (2018) proved `≤ 2.37` with a
large computer search; Baek (2024, preprint) claims the exact value `= area(Gerver)`.) -/
theorem sofaConstant_le_two_mul_sqrt_two :
    sofaConstant ≤ ENNReal.ofReal (2 * Real.sqrt 2) := by
  unfold sofaConstant
  exact iSup₂_le fun s hs => by
    obtain ⟨m, hm⟩ := hs
    exact volume_le_of_isMovingSofa hm

/-- In particular the sofa constant is finite (not `⊤`). -/
theorem sofaConstant_ne_top : sofaConstant ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top sofaConstant_le_two_mul_sqrt_two

/-! ## Statement (only) of Baek's theorem

The upstream repository states Gerver's optimality as
`sofaConstant_eq_volume_gerversSofa : sofaConstant = volume gerversSofa` (with `sorry`),
where `gerversSofa` is built from Gerver's explicit rotation path.  A Lean proof would require
formalizing Baek, *Optimality of Gerver's Sofa* (arXiv:2411.19826, 119 pages): monotone-sofa
reduction, cap/niche decomposition, the concave upper-bound functional `Q` (Brunn–Minkowski /
Mamikon), and Romik's local-optimality ODE analysis.  None of that is attempted here; the
Hammersley bound above is the only *proved* upper bound in this file. -/

end MovingSofa
