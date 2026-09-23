/-
# Sofa/Monotone.lean — from the upstream motion to Baek's hallway family; the monotone hull
(M2, batch 2: Baek §2.3, Def 2.3.5 and the first half of Theorem 2.3.2)

Conventions.  For an upstream motion `m` with rotation angle `θ` (`exists_rotationAngle`),
`m t p = rot (θ t) p + m t 0`.  In the sofa's own frame the hallway at time `t` is
`R_{-θ t}(L) + c`, so Baek's parameter is `-θ t`; a sofa turning the corner the natural way has
`θ 1 = -ω` with Baek's rotation angle `ω ∈ (0, π/2]`.

Naming.  Lemmas *about the upstream structure* `MovingSofa.IsMovingSofa` are declared in the
namespace `MovingSofa.IsMovingSofa` (so that dot notation `hm.isBounded` works — Lean only
searches the namespace of the head constant of the type); everything else lives in `Sofa`.

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 2 (2026-09-17, Opus 5), compiled locally (Lean 4.33.1,
Mathlib v4.33.1 subset imports), no `sorry`.  Round 1 (Fable 5.1) was never compiled; a static review found that every
`hm.foo` call was broken (the lemmas lived in `Sofa.IsMovingSofa`, but dot notation only searches
`MovingSofa.IsMovingSofa`).  Round 2 fixes that and replaces the `sorry` in `isBounded` by a proof
(Hammersley-style case split).
-/
import Sofa.Support

noncomputable section

open Real Set MovingSofa
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

/-! ## Every moving sofa is bounded -/

namespace MovingSofa

/-- A point of the unit horizontal strip that also lies in a slanted unit strip with `n₁ ≠ 0`
has bounded first coordinate. -/
lemma abs_le_of_mem_strip {n₁ n₂ a x y : ℝ} (hn : n₁ ≠ 0) (h1 : a ≤ n₁ * x + n₂ * y)
    (h2 : n₁ * x + n₂ * y ≤ a + 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    |x| ≤ (|a| + 1 + |n₂|) / |n₁| := by
  rw [le_div_iff₀ (abs_pos.mpr hn), mul_comm, ← abs_mul]
  have hy : |n₂ * y| ≤ |n₂| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr ⟨by linarith, hy1⟩)
  have ha := abs_le.mp (le_refl |a|)
  have hy' := abs_le.mp hy
  rw [abs_le]
  constructor <;> linarith [ha.1, ha.2, hy'.1, hy'.2]

/-- A set inside the unit horizontal strip and inside a slanted unit strip (`n₁ ≠ 0`) is
bounded. -/
lemma isBounded_of_forall_mem_strip (S : Set ℝ²) (n₁ n₂ a : ℝ) (hn : n₁ ≠ 0)
    (h : ∀ q ∈ S, a ≤ n₁ * q 0 + n₂ * q 1 ∧ n₁ * q 0 + n₂ * q 1 ≤ a + 1)
    (hS : ∀ q ∈ S, 0 ≤ q 1 ∧ q 1 ≤ 1) : Bornology.IsBounded S := by
  have hC0 : 0 ≤ (|a| + 1 + |n₂|) / |n₁| := div_nonneg (by positivity) (abs_nonneg _)
  refine isBounded_iff_forall_norm_le.2 ⟨(|a| + 1 + |n₂|) / |n₁| + 1, fun q hq => ?_⟩
  obtain ⟨h1, h2⟩ := h q hq
  obtain ⟨h3, h4⟩ := hS q hq
  have hx := abs_le_of_mem_strip hn h1 h2 h3 h4
  have hx2 : q 0 ^ 2 ≤ ((|a| + 1 + |n₂|) / |n₁|) ^ 2 := by
    rw [← sq_abs (q 0)]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hy2 : q 1 ^ 2 ≤ 1 := by nlinarith
  have hn2 : ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rw [← sq_le_sq₀ (norm_nonneg q) (by positivity)]
  nlinarith

/-- **Every moving sofa is bounded** (the upstream definition does not ask for it).

Same case split as Hammersley's bound: if `cos θ(1) ≠ 0` the final vertical strip is a slanted
strip in the sofa's frame; otherwise `cos θ(t) = 1/2` at some time `t` (IVT), and then both arms
of the hallway are slanted strips. -/
theorem IsMovingSofa.isBounded {s : Set ℝ²} {m : I → E(2)} (hm : IsMovingSofa s m) :
    Bornology.IsBounded s := by
  have hS : ∀ q ∈ s, 0 ≤ q 1 ∧ q 1 ≤ 1 := fun q hq =>
    ((mem_horizontalHallway_iff q).1 (hm.initial hq)).2
  have hc : Continuous fun t : I => ((m t).linearIsometryEquiv e₀) 0 :=
    continuous_linear_coord hm.continuous e₀ 0
  have hc0 : ((m 0).linearIsometryEquiv e₀) 0 = 1 := by
    have h : ((m 0).linearIsometryEquiv e₀) 0 = (m 0 e₀) 0 - (m 0 0) 0 := by
      rw [apply_eq_linear_add (m 0) e₀, PiLp.add_apply]
      ring
    rw [h, hm.zero]
    show e₀ 0 - (0 : ℝ²) 0 = 1
    simp [e₀, PiLp.toLp_apply]
  by_cases hA : ((m 1).linearIsometryEquiv e₀) 0 = 0
  · have hle1 : ((m 1).linearIsometryEquiv e₀) 0 ≤ 1 / 2 := by rw [hA]; norm_num
    have hle0 : (1 / 2 : ℝ) ≤ ((m 0).linearIsometryEquiv e₀) 0 := by rw [hc0]; norm_num
    obtain ⟨t, ht⟩ : ∃ t : I, ((m t).linearIsometryEquiv e₀) 0 = 1 / 2 :=
      intermediate_value_univ 1 0 hc ⟨hle1, hle0⟩
    have hsn : ((m t).linearIsometryEquiv e₀) 1 ≠ 0 := by
      intro h0
      have h := sq_add_sq_eq_one (m t).linearIsometryEquiv
      rw [ht, h0] at h
      norm_num at h
    have hcn : ((m t).linearIsometryEquiv e₀) 0 ≠ 0 := by rw [ht]; norm_num
    have hcover : s ⊆ {q ∈ s | 0 ≤ (m t q) 1 ∧ (m t q) 1 ≤ 1}
        ∪ {q ∈ s | 0 ≤ (m t q) 0 ∧ (m t q) 0 ≤ 1} := by
      intro q hq
      have h : m t q ∈ horizontalHallway ∪ verticalHallway := hm.subset_hallway t ⟨q, hq, rfl⟩
      rcases h with h | h
      · exact Or.inl ⟨hq, ((mem_horizontalHallway_iff _).1 h).2⟩
      · have h' := (mem_verticalHallway_iff _).1 h
        exact Or.inr ⟨hq, h'.1, h'.2.1⟩
    refine Bornology.IsBounded.subset (Bornology.IsBounded.union ?_ ?_) hcover
    · refine isBounded_of_forall_mem_strip _ (((m t).linearIsometryEquiv e₀) 1)
        (((m t).linearIsometryEquiv e₁) 1) (-(m t 0) 1) hsn (fun q hq => ?_)
        (fun q hq => hS q hq.1)
      have h := apply_coord (m t) q 1
      obtain ⟨-, h0, h1⟩ := hq
      constructor <;> linarith
    · refine isBounded_of_forall_mem_strip _ (((m t).linearIsometryEquiv e₀) 0)
        (((m t).linearIsometryEquiv e₁) 0) (-(m t 0) 0) hcn (fun q hq => ?_)
        (fun q hq => hS q hq.1)
      have h := apply_coord (m t) q 0
      obtain ⟨-, h0, h1⟩ := hq
      constructor <;> linarith
  · -- the final vertical strip is a slanted strip in the sofa's frame
    refine isBounded_of_forall_mem_strip s (((m 1).linearIsometryEquiv e₀) 0)
      (((m 1).linearIsometryEquiv e₁) 0) (-(m 1 0) 0) hA (fun q hq => ?_) hS
    have h := apply_coord (m 1) q 0
    have h' := (mem_verticalHallway_iff (m 1 q)).1 (hm.final ⟨q, hq, rfl⟩)
    constructor <;> linarith [h'.1, h'.2.1]

theorem IsMovingSofa.isCompact {s : Set ℝ²} {m : I → E(2)} (hm : IsMovingSofa s m) :
    IsCompact s :=
  Metric.isCompact_of_isClosed_isBounded hm.isClosed hm.isBounded

theorem IsMovingSofa.nonempty {s : Set ℝ²} {m : I → E(2)} (hm : IsMovingSofa s m) :
    s.Nonempty :=
  hm.isConnected.nonempty

end MovingSofa

namespace Sofa

lemma rot_neg (t : ℝ) (p : ℝ²) : rot t (-p) = -(rot t p) := by
  ext i; fin_cases i <;> simp <;> ring

/-! ## Bridge: the upstream hallway condition in the sofa's frame -/

/-- At time `t` the sofa lies in the translate `R_{-θ t}(L) + c_t` of the rotated hallway. -/
theorem _root_.MovingSofa.IsMovingSofa.subset_rot_hallway {s : Set ℝ²} {m : I → E(2)}
    (hm : IsMovingSofa s m) {θ : I → ℝ} (hθ : ∀ t p, m t p = rot (θ t) p + m t 0) (t : I) :
    s ⊆ (fun p => rot (-(θ t)) p + -(rot (-(θ t)) (m t 0))) '' (Qplus \ Qminus) := by
  intro p hp
  refine ⟨m t p, ?_, ?_⟩
  · have h := hm.subset_hallway t ⟨p, hp, rfl⟩
    rwa [hallway_eq_diff] at h
  · show rot (-(θ t)) (m t p) + -(rot (-(θ t)) (m t 0)) = p
    rw [hθ t p, rot_add, rot_neg_rot]
    abel

/-- **Prop 2.2.3 applied along the motion**: at every time the sofa lies in its own supporting
hallway with parameter `-θ t`. -/
theorem _root_.MovingSofa.IsMovingSofa.subset_suppHallway {s : Set ℝ²} {m : I → E(2)}
    (hm : IsMovingSofa s m) {θ : I → ℝ} (hθ : ∀ t p, m t p = rot (θ t) p + m t 0) (t : I) :
    s ⊆ suppHallway s (-(θ t)) :=
  Sofa.subset_suppHallway hm.isCompact hm.nonempty (-(θ t)) _ (hm.subset_rot_hallway hθ t)

/-! ## The monotone hull `𝓘(S)` (Def 2.3.5) -/

/-- The two unit strips bounded by the supporting lines of `S` at angles `π/2` and `ω`
(Baek's `P_ω = H ∩ V_ω` after normalisation `h_S(π/2) = h_S(ω) = 1`). -/
def strips (S : Set ℝ²) (ω : ℝ) : Set ℝ² :=
  (hpLe (π / 2) (supportFn S (π / 2)) ∩ hpGe (π / 2) (supportFn S (π / 2) - 1)) ∩
    (hpLe ω (supportFn S ω) ∩ hpGe ω (supportFn S ω - 1))

/-- The monotone hull `𝓘(S) = P_ω ∩ ⋂_{t ∈ [0, ω]} L_S(t)`. -/
def monotoneHull (S : Set ℝ²) (ω : ℝ) : Set ℝ² :=
  strips S ω ∩ ⋂ t ∈ Icc (0 : ℝ) ω, suppHallway S t

lemma isClosed_QplusS (S : Set ℝ²) (t : ℝ) : IsClosed (QplusS S t) :=
  (isClosed_hpLe _ _).inter (isClosed_hpLe _ _)

lemma isOpen_QminusS (S : Set ℝ²) (t : ℝ) : IsOpen (QminusS S t) :=
  (isOpen_hpLt _ _).inter (isOpen_hpLt _ _)

lemma isClosed_suppHallway (S : Set ℝ²) (t : ℝ) : IsClosed (suppHallway S t) := by
  rw [suppHallway_eq]; exact (isClosed_QplusS S t).sdiff (isOpen_QminusS S t)

lemma isClosed_strips (S : Set ℝ²) (ω : ℝ) : IsClosed (strips S ω) :=
  ((isClosed_hpLe _ _).inter (isClosed_hpGe _ _)).inter
    ((isClosed_hpLe _ _).inter (isClosed_hpGe _ _))

lemma isClosed_monotoneHull (S : Set ℝ²) (ω : ℝ) : IsClosed (monotoneHull S ω) :=
  (isClosed_strips S ω).inter (isClosed_biInter fun t _ => isClosed_suppHallway S t)

lemma monotoneHull_subset_suppHallway (S : Set ℝ²) {ω t : ℝ} (ht : t ∈ Icc (0 : ℝ) ω) :
    monotoneHull S ω ⊆ suppHallway S t := fun p hp => by
  have h := hp.2
  rw [Set.mem_iInter₂] at h
  exact h t ht

/-- **Theorem 2.3.2 (first half)**: a moving sofa whose rotation angle ends at `θ 1 = -ω`
is contained in its monotone hull `𝓘(S)`.  (No sign condition on `ω` is needed: for `ω < 0`
the intersection over `[0, ω]` is empty.) -/
theorem _root_.MovingSofa.IsMovingSofa.subset_monotoneHull {s : Set ℝ²} {m : I → E(2)}
    (hm : IsMovingSofa s m) {θ : I → ℝ} (hθc : Continuous θ) (hθ0 : θ 0 = 0)
    (hθ : ∀ t p, m t p = rot (θ t) p + m t 0) {ω : ℝ} (hω : θ 1 = -ω) :
    s ⊆ monotoneHull s ω := by
  have hc := hm.isCompact
  have hne := hm.nonempty
  intro p hp
  refine ⟨⟨⟨le_supportFn hc hp _, ?_⟩, ⟨le_supportFn hc hp _, ?_⟩⟩, ?_⟩
  · -- the horizontal strip: `h_s(π/2) ≤ 1` and `0 ≤ p 1`
    have hp1 := ((mem_horizontalHallway_iff p).1 (hm.initial hp)).2.1
    have hle : supportFn s (π / 2) ≤ 1 := by
      rw [supportFn_le_iff hc hne]
      intro q hq
      rw [inner_u_pi_div_two]
      exact ((mem_horizontalHallway_iff q).1 (hm.initial hq)).2.2
    show supportFn s (π / 2) - 1 ≤ ⟪p, u (π / 2)⟫
    rw [inner_u_pi_div_two]
    linarith
  · -- the final vertical strip, seen at angle `ω = -θ 1`
    have key : ∀ q ∈ s, 0 ≤ ⟪q, u ω⟫ + (m 1 0) 0 ∧ ⟪q, u ω⟫ + (m 1 0) 0 ≤ 1 := by
      intro q hq
      have h := (mem_verticalHallway_iff (m 1 q)).1 (hm.final ⟨q, hq, rfl⟩)
      have e : (m 1 q) 0 = ⟪q, u ω⟫ + (m 1 0) 0 := by
        rw [hθ 1 q, PiLp.add_apply, ← inner_u_zero, inner_rot_u, zero_sub, hω, neg_neg]
      rw [e] at h
      exact ⟨h.1, h.2.1⟩
    have hle : supportFn s ω ≤ 1 - (m 1 0) 0 := by
      rw [supportFn_le_iff hc hne]
      intro q hq
      linarith [(key q hq).2]
    show supportFn s ω - 1 ≤ ⟪p, u ω⟫
    linarith [(key p hp).1]
  · -- every angle `t ∈ [0, ω]` is attained by `-θ` (IVT), then Prop 2.2.3
    rw [Set.mem_iInter₂]
    intro t ht
    have hIVT := intermediate_value_univ 1 0 hθc
    have hmem : -t ∈ Icc (θ 1) (θ 0) := by
      rw [hω, hθ0, Set.mem_Icc]
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    obtain ⟨t₀, ht₀⟩ := hIVT hmem
    have h := hm.subset_suppHallway hθ t₀ hp
    rwa [ht₀, neg_neg] at h

end Sofa
