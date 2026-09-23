/-
# Sofa/Support.lean — support functions and supporting hallways (Baek §2.1–2.2)

STATUS: [PROOF-C] [AXIOM-CHECK] (round 4 compiled on the user's machine, 2026-09-17, full
Mathlib; no `sorry`).  Performance note: that build took 751 s on the user's machine, but only
2.7 s in the cloud dev tree with subset imports — the slowdown is specific to `import Mathlib`
and is still to be profiled (PLAN.md risk R10).
-/
import Sofa.Basic

noncomputable section

open Real Set
open scoped EuclideanGeometry RealInnerProductSpace Pointwise

namespace Sofa

/-! ## Two more rotation identities (used below) -/

lemma inner_rot_u_self (t : ℝ) (q : ℝ²) : ⟪rot t q, u t⟫ = q 0 := by
  rw [inner_rot_u, sub_self, inner_u_zero]

lemma inner_rot_u_add_pi_div_two (t : ℝ) (q : ℝ²) : ⟪rot t q, u (t + π / 2)⟫ = q 1 := by
  rw [inner_rot_u]
  have h : t + π / 2 - t = π / 2 := by ring
  rw [h, inner_u_pi_div_two]

lemma mem_Qplus_iff (q : ℝ²) : q ∈ Qplus ↔ q 0 ≤ 1 ∧ q 1 ≤ 1 := Iff.rfl
lemma mem_Qminus_iff (q : ℝ²) : q ∈ Qminus ↔ q 0 < 0 ∧ q 1 < 0 := Iff.rfl

/-! ## Support function (Def 2.1.6) -/

/-- Projection onto the direction `u_t`. -/
def proj (t : ℝ) (p : ℝ²) : ℝ := ⟪p, u t⟫

lemma continuous_proj (t : ℝ) : Continuous (proj t) := continuous_inner_u t

/-- The support function `h_S(t) = sup {⟪s, u_t⟫ : s ∈ S}` of a nonempty compact `S`.
(For `S` empty or unbounded this is junk: `sSup ∅ = 0` in `ℝ`.) -/
def supportFn (S : Set ℝ²) (t : ℝ) : ℝ := sSup (proj t '' S)

section
variable {S : Set ℝ²} (hS : IsCompact S) (hne : S.Nonempty)
include hS

lemma bddAbove_proj_image (t : ℝ) : BddAbove (proj t '' S) :=
  hS.bddAbove_image (continuous_proj t).continuousOn

/-- `⟪p, u_t⟫ ≤ h_S(t)` for every `p ∈ S`. -/
lemma le_supportFn {p : ℝ²} (hp : p ∈ S) (t : ℝ) : ⟪p, u t⟫ ≤ supportFn S t :=
  le_csSup (bddAbove_proj_image hS t) ⟨p, hp, rfl⟩

/-- `S ⊆ H_S(t)`: every compact set lies in its supporting half-planes. -/
lemma subset_hpLe_supportFn (t : ℝ) : S ⊆ hpLe t (supportFn S t) :=
  fun _ hp => le_supportFn hS hp t

include hne in
/-- The supremum is attained (Weierstrass). -/
lemma exists_supportFn_eq (t : ℝ) : ∃ p ∈ S, ⟪p, u t⟫ = supportFn S t := by
  obtain ⟨p, hp, h⟩ := hS.exists_sSup_image_eq hne (continuous_proj t).continuousOn
  exact ⟨p, hp, h.symm⟩

include hne in
lemma supportFn_le_iff (t a : ℝ) : supportFn S t ≤ a ↔ ∀ p ∈ S, ⟪p, u t⟫ ≤ a := by
  constructor
  · intro h p hp; exact (le_supportFn hS hp t).trans h
  · intro h
    unfold supportFn
    apply csSup_le (hne.image _)
    rintro _ ⟨p, hp, rfl⟩
    exact h p hp

end

/-- Monotonicity in the set. -/
lemma supportFn_mono {S T : Set ℝ²} (hT : IsCompact T) (hne : S.Nonempty) (h : S ⊆ T) (t : ℝ) :
    supportFn S t ≤ supportFn T t := by
  unfold supportFn
  exact csSup_le_csSup (bddAbove_proj_image hT t) (hne.image _) (Set.image_mono h)

/-- `2π`-periodicity. -/
lemma supportFn_add_two_pi (S : Set ℝ²) (t : ℝ) : supportFn S (t + 2 * π) = supportFn S t := by
  unfold supportFn proj; rw [u_add_two_pi]

/-- Support function of a translate: `h_{S+q}(t) = h_S(t) + ⟪q, u_t⟫`. -/
lemma supportFn_translate {S : Set ℝ²} (hS : IsCompact S) (hne : S.Nonempty) (q : ℝ²) (t : ℝ) :
    supportFn ((fun p => p + q) '' S) t = supportFn S t + ⟪q, u t⟫ := by
  have hS' : IsCompact ((fun p => p + q) '' S) := hS.image (by fun_prop)
  have hne' : ((fun p => p + q) '' S).Nonempty := hne.image _
  apply le_antisymm
  · rw [supportFn_le_iff hS' hne']
    rintro _ ⟨p, hp, rfl⟩
    show ⟪p + q, u t⟫ ≤ supportFn S t + ⟪q, u t⟫
    rw [inner_add_left]
    linarith [le_supportFn hS hp t]
  · obtain ⟨p, hp, hpe⟩ := exists_supportFn_eq hS hne t
    have h : ⟪p + q, u t⟫ ≤ supportFn ((fun p => p + q) '' S) t :=
      le_supportFn hS' (Set.mem_image_of_mem (fun p => p + q) hp) t
    rw [inner_add_left, hpe] at h
    exact h

/-- Support function of a Minkowski sum: `h_{S+T} = h_S + h_T`. -/
lemma supportFn_add {S T : Set ℝ²} (hS : IsCompact S) (hT : IsCompact T)
    (hSne : S.Nonempty) (hTne : T.Nonempty) (t : ℝ) :
    supportFn (S + T) t = supportFn S t + supportFn T t := by
  have hST : IsCompact (S + T) := hS.add hT
  have hSTne : (S + T).Nonempty := hSne.add hTne
  apply le_antisymm
  · rw [supportFn_le_iff hST hSTne]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    show ⟪a + b, u t⟫ ≤ supportFn S t + supportFn T t
    rw [inner_add_left]
    exact add_le_add (le_supportFn hS ha t) (le_supportFn hT hb t)
  · obtain ⟨a, ha, hae⟩ := exists_supportFn_eq hS hSne t
    obtain ⟨b, hb, hbe⟩ := exists_supportFn_eq hT hTne t
    have h : ⟪a + b, u t⟫ ≤ supportFn (S + T) t :=
      le_supportFn hST (Set.add_mem_add ha hb) t
    rw [inner_add_left, hae, hbe] at h
    exact h

/-! ## Supporting lines, half-planes, width (Def 2.1.7, 2.1.8) -/

/-- `l_S(t)`. -/
def supportLine (S : Set ℝ²) (t : ℝ) : Set ℝ² := line t (supportFn S t)
/-- `H_S(t)`. -/
def supportHalfPlane (S : Set ℝ²) (t : ℝ) : Set ℝ² := hpLe t (supportFn S t)
/-- The width of `S` in direction `t`: `h_S(t) + h_S(t + π)`. -/
def width (S : Set ℝ²) (t : ℝ) : ℝ := supportFn S t + supportFn S (t + π)
/-- The edge `e_S(t) = S ∩ l_S(t)` (Def 2.1.9). -/
def edge (S : Set ℝ²) (t : ℝ) : Set ℝ² := S ∩ supportLine S t

lemma edge_nonempty {S : Set ℝ²} (hS : IsCompact S) (hne : S.Nonempty) (t : ℝ) :
    (edge S t).Nonempty := by
  obtain ⟨p, hp, h⟩ := exists_supportFn_eq hS hne t
  exact ⟨p, hp, h⟩

/-! ## The supporting hallway `L_S(t)` (Def 2.2.2, 2.2.3) -/

/-- `f_{S,t}(p) = R_t p + (h_S(t) - 1) u_t + (h_S(t + π/2) - 1) v_t`. -/
def suppMap (S : Set ℝ²) (t : ℝ) (p : ℝ²) : ℝ² :=
  rot t p + (supportFn S t - 1) • u t + (supportFn S (t + π / 2) - 1) • v t

/-- The supporting hallway `L_S(t) = f_{S,t}(L)`. -/
def suppHallway (S : Set ℝ²) (t : ℝ) : Set ℝ² := suppMap S t '' (Qplus \ Qminus)

/-- Inner corner `x_S(t)`. -/
def innerCorner (S : Set ℝ²) (t : ℝ) : ℝ² :=
  (supportFn S t - 1) • u t + (supportFn S (t + π / 2) - 1) • v t
/-- Outer corner `y_S(t)`. -/
def outerCorner (S : Set ℝ²) (t : ℝ) : ℝ² :=
  supportFn S t • u t + supportFn S (t + π / 2) • v t
/-- Outer quarter-plane `Q_S⁺(t) = H_S(t) ∩ H_S(t + π/2)`. -/
def QplusS (S : Set ℝ²) (t : ℝ) : Set ℝ² :=
  hpLe t (supportFn S t) ∩ hpLe (t + π / 2) (supportFn S (t + π / 2))
/-- Inner open quarter-plane `Q_S⁻(t)`. -/
def QminusS (S : Set ℝ²) (t : ℝ) : Set ℝ² :=
  hpLt t (supportFn S t - 1) ∩ hpLt (t + π / 2) (supportFn S (t + π / 2) - 1)
/-- Outer walls `a_S(t)`, `c_S(t)` and inner walls `b_S(t)`, `d_S(t)` (as lines). -/
def wallA (S : Set ℝ²) (t : ℝ) : Set ℝ² := line t (supportFn S t)
def wallC (S : Set ℝ²) (t : ℝ) : Set ℝ² := line (t + π / 2) (supportFn S (t + π / 2))
def wallB (S : Set ℝ²) (t : ℝ) : Set ℝ² := line t (supportFn S t - 1)
def wallD (S : Set ℝ²) (t : ℝ) : Set ℝ² := line (t + π / 2) (supportFn S (t + π / 2) - 1)

lemma mem_QplusS_iff (S : Set ℝ²) (t : ℝ) (p : ℝ²) :
    p ∈ QplusS S t ↔
      ⟪p, u t⟫ ≤ supportFn S t ∧ ⟪p, u (t + π / 2)⟫ ≤ supportFn S (t + π / 2) :=
  Iff.rfl

lemma mem_QminusS_iff (S : Set ℝ²) (t : ℝ) (p : ℝ²) :
    p ∈ QminusS S t ↔
      ⟪p, u t⟫ < supportFn S t - 1 ∧ ⟪p, u (t + π / 2)⟫ < supportFn S (t + π / 2) - 1 :=
  Iff.rfl

/-- The two coordinates of `f_{S,t}(q)` in the frame `(u_t, v_t)`. -/
lemma inner_suppMap_u (S : Set ℝ²) (t : ℝ) (q : ℝ²) :
    ⟪suppMap S t q, u t⟫ = q 0 + (supportFn S t - 1) := by
  unfold suppMap
  rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_u_u, inner_v_u, inner_rot_u, sub_self, inner_u_zero]
  ring

lemma inner_suppMap_v (S : Set ℝ²) (t : ℝ) (q : ℝ²) :
    ⟪suppMap S t q, u (t + π / 2)⟫ = q 1 + (supportFn S (t + π / 2) - 1) := by
  unfold suppMap
  rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    u_add_pi_div_two, inner_u_v, inner_v_v, ← u_add_pi_div_two, inner_rot_u]
  have h : t + π / 2 - t = π / 2 := by ring
  rw [h, inner_u_pi_div_two]
  ring

lemma suppMap_injective (S : Set ℝ²) (t : ℝ) : Function.Injective (suppMap S t) := by
  intro p q h
  unfold suppMap at h
  exact rot_injective t (add_right_cancel (add_right_cancel h))

/-- The inverse of `f_{S,t}`: `p ↦ R_{-t}(p - x_S(t))`. -/
def suppMapInv (S : Set ℝ²) (t : ℝ) (p : ℝ²) : ℝ² := rot (-t) (p - innerCorner S t)

lemma suppMap_suppMapInv (S : Set ℝ²) (t : ℝ) (p : ℝ²) :
    suppMap S t (suppMapInv S t p) = p := by
  unfold suppMap suppMapInv innerCorner
  rw [rot_rot, add_neg_cancel, rot_zero]
  abel

lemma suppMap_image_Qplus (S : Set ℝ²) (t : ℝ) : suppMap S t '' Qplus = QplusS S t := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨hq0, hq1⟩ := (mem_Qplus_iff q).1 hq
    rw [mem_QplusS_iff, inner_suppMap_u, inner_suppMap_v]
    constructor <;> linarith
  · intro hp
    obtain ⟨hp1, hp2⟩ := (mem_QplusS_iff S t p).1 hp
    refine ⟨suppMapInv S t p, ?_, suppMap_suppMapInv S t p⟩
    have e1 := inner_suppMap_u S t (suppMapInv S t p)
    have e2 := inner_suppMap_v S t (suppMapInv S t p)
    rw [suppMap_suppMapInv] at e1 e2
    rw [mem_Qplus_iff]
    constructor <;> linarith

lemma suppMap_image_Qminus (S : Set ℝ²) (t : ℝ) : suppMap S t '' Qminus = QminusS S t := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨hq0, hq1⟩ := (mem_Qminus_iff q).1 hq
    rw [mem_QminusS_iff, inner_suppMap_u, inner_suppMap_v]
    constructor <;> linarith
  · intro hp
    obtain ⟨hp1, hp2⟩ := (mem_QminusS_iff S t p).1 hp
    refine ⟨suppMapInv S t p, ?_, suppMap_suppMapInv S t p⟩
    have e1 := inner_suppMap_u S t (suppMapInv S t p)
    have e2 := inner_suppMap_v S t (suppMapInv S t p)
    rw [suppMap_suppMapInv] at e1 e2
    rw [mem_Qminus_iff]
    constructor <;> linarith

/-- **Prop 2.2.2**: `L_S(t) = Q_S⁺(t) \ Q_S⁻(t)`. -/
theorem suppHallway_eq (S : Set ℝ²) (t : ℝ) : suppHallway S t = QplusS S t \ QminusS S t := by
  unfold suppHallway
  rw [Set.image_sdiff (suppMap_injective S t), suppMap_image_Qplus, suppMap_image_Qminus]

/-- **Prop 2.2.3**: if a nonempty compact `S` is contained in some translate of `R_t(L)`,
then it is contained in its own supporting hallway `L_S(t)`. -/
theorem subset_suppHallway {S : Set ℝ²} (hS : IsCompact S) (hne : S.Nonempty) (t : ℝ)
    (c : ℝ²) (h : S ⊆ (fun p => rot t p + c) '' (Qplus \ Qminus)) : S ⊆ suppHallway S t := by
  rw [suppHallway_eq]
  -- the outer walls of `L'` bound the support function
  have hu : supportFn S t ≤ 1 + ⟪c, u t⟫ := by
    rw [supportFn_le_iff hS hne]
    intro p hp
    obtain ⟨q, ⟨hq, -⟩, hpq⟩ := h hp
    have hpq' : rot t q + c = p := hpq
    rw [← hpq', inner_add_left, inner_rot_u_self]
    have hq' := (mem_Qplus_iff q).1 hq
    linarith [hq'.1]
  have hv : supportFn S (t + π / 2) ≤ 1 + ⟪c, u (t + π / 2)⟫ := by
    rw [supportFn_le_iff hS hne]
    intro p hp
    obtain ⟨q, ⟨hq, -⟩, hpq⟩ := h hp
    have hpq' : rot t q + c = p := hpq
    rw [← hpq', inner_add_left, inner_rot_u_add_pi_div_two]
    have hq' := (mem_Qplus_iff q).1 hq
    linarith [hq'.2]
  intro p hp
  refine ⟨⟨le_supportFn hS hp t, le_supportFn hS hp (t + π / 2)⟩, ?_⟩
  intro hneg
  obtain ⟨h1, h2⟩ := (mem_QminusS_iff S t p).1 hneg
  obtain ⟨q, ⟨_, hqn⟩, hpq⟩ := h hp
  have hpq' : rot t q + c = p := hpq
  rw [← hpq', inner_add_left, inner_rot_u_self] at h1
  rw [← hpq', inner_add_left, inner_rot_u_add_pi_div_two] at h2
  apply hqn
  rw [mem_Qminus_iff]
  constructor <;> linarith

/-- The outer corner is the inner corner shifted by `u_t + v_t`. -/
lemma outerCorner_eq (S : Set ℝ²) (t : ℝ) :
    outerCorner S t = innerCorner S t + u t + v t := by
  unfold outerCorner innerCorner
  rw [sub_smul, sub_smul, one_smul, one_smul]
  abel

end Sofa
