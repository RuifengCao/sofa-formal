/-
# Sofa/StdPos.lean — Baek's moving sofas with a rotation angle; standard position
(M2 batch 3: Baek Def 1.1.2, Def 2.3.3, Def 2.3.4, Prop 1.2.1 = Prop 2.3.1, Prop 1.2.2)

* `tr c S` — the translate `S + c`, and how support functions, supporting hallways, strips and
  the monotone hull transform under it;
* `StdPos S ω` — standard position `h_S(ω) = h_S(π/2) = 1` (Def 2.3.4), and the translation
  `stdVec S ω` achieving it (Prop 2.3.1, existence part);
* `IsSofaWithAngle S ω` — some translate of `S` is an upstream moving sofa whose motion has
  continuous rotation angle `θ` with `θ 1 = -ω` (Baek's "moving sofa with rotation angle ω");
* `IsSofaWithAngle.subset` — Prop 1.2.2 in normalised form:
  `S ⊆ P_ω` and `S ⊆ L_S(t)` for all `t ∈ [0, ω]`.

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 1 (2026-09-17, Opus 5), no `sorry`.
-/
import Sofa.Monotone
import Sofa.Motion

noncomputable section

open Real Set MovingSofa MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa

/-! ## Translations -/

/-- The translate `S + c`. -/
def tr (c : ℝ²) (S : Set ℝ²) : Set ℝ² := (· + c) '' S

variable {S : Set ℝ²} {ω : ℝ}

lemma mem_tr {c p : ℝ²} : p ∈ tr c S ↔ p - c ∈ S := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro h
    exact ⟨p - c, h, by simp⟩

lemma add_mem_tr {c p : ℝ²} (hp : p ∈ S) : p + c ∈ tr c S := ⟨p, hp, rfl⟩

lemma tr_tr (c d : ℝ²) (S : Set ℝ²) : tr d (tr c S) = tr (c + d) S := by
  ext p
  simp only [mem_tr]
  rw [show p - d - c = p - (c + d) by abel]

lemma tr_zero (S : Set ℝ²) : tr 0 S = S := by
  ext p; simp [mem_tr]

lemma tr_neg_tr (c : ℝ²) (S : Set ℝ²) : tr (-c) (tr c S) = S := by
  rw [tr_tr, add_neg_cancel, tr_zero]

lemma tr_mono {c : ℝ²} {S T : Set ℝ²} (h : S ⊆ T) : tr c S ⊆ tr c T := Set.image_mono h

lemma tr_inter (c : ℝ²) (S T : Set ℝ²) : tr c (S ∩ T) = tr c S ∩ tr c T :=
  Set.image_inter (add_left_injective c)

lemma tr_sdiff (c : ℝ²) (S T : Set ℝ²) : tr c (S \ T) = tr c S \ tr c T :=
  Set.image_sdiff (add_left_injective c) S T

lemma tr_biInter {ι : Type*} (c : ℝ²) (A : Set ι) (F : ι → Set ℝ²) :
    tr c (⋂ i ∈ A, F i) = ⋂ i ∈ A, tr c (F i) := by
  ext p
  simp only [mem_tr, Set.mem_iInter₂]

lemma isCompact_tr (hS : IsCompact S) (c : ℝ²) : IsCompact (tr c S) :=
  hS.image (by fun_prop)

lemma nonempty_tr (hS : S.Nonempty) (c : ℝ²) : (tr c S).Nonempty := hS.image _

lemma isConnected_tr (hS : IsConnected S) (c : ℝ²) : IsConnected (tr c S) :=
  hS.image _ (by fun_prop : Continuous fun p : ℝ² => p + c).continuousOn

lemma isClosed_tr (hS : IsClosed S) (c : ℝ²) : IsClosed (tr c S) :=
  (Homeomorph.addRight c).isClosedMap _ hS

lemma volume_tr (c : ℝ²) (S : Set ℝ²) : volume (tr c S) = volume S := by
  rw [tr, Set.image_add_right, measure_preimage_add_right]

lemma supportFn_tr (hS : IsCompact S) (hne : S.Nonempty) (c : ℝ²) (t : ℝ) :
    supportFn (tr c S) t = supportFn S t + ⟪c, u t⟫ :=
  supportFn_translate hS hne c t

/-- Half-planes under translation. -/
lemma tr_hpLe (c : ℝ²) (t h : ℝ) : tr c (hpLe t h) = hpLe t (h + ⟪c, u t⟫) := by
  ext p
  simp only [mem_tr, hpLe, Set.mem_ofPred_eq, inner_sub_left]
  constructor <;> intro hp <;> linarith

lemma tr_hpGe (c : ℝ²) (t h : ℝ) : tr c (hpGe t h) = hpGe t (h + ⟪c, u t⟫) := by
  ext p
  simp only [mem_tr, hpGe, Set.mem_ofPred_eq, inner_sub_left]
  constructor <;> intro hp <;> linarith

lemma suppMap_tr (hS : IsCompact S) (hne : S.Nonempty) (c : ℝ²) (t : ℝ) (p : ℝ²) :
    suppMap (tr c S) t p = suppMap S t p + c := by
  unfold suppMap
  rw [supportFn_tr hS hne, supportFn_tr hS hne, u_add_pi_div_two]
  conv_rhs => rw [decomp_u_v t c]
  module

lemma suppHallway_tr (hS : IsCompact S) (hne : S.Nonempty) (c : ℝ²) (t : ℝ) :
    suppHallway (tr c S) t = tr c (suppHallway S t) := by
  unfold suppHallway tr
  rw [Set.image_image]
  exact Set.image_congr fun p _ => suppMap_tr hS hne c t p

lemma QplusS_tr (hS : IsCompact S) (hne : S.Nonempty) (c : ℝ²) (t : ℝ) :
    QplusS (tr c S) t = tr c (QplusS S t) := by
  rw [← suppMap_image_Qplus, ← suppMap_image_Qplus]
  show _ = (· + c) '' (suppMap S t '' Qplus)
  rw [Set.image_image]
  exact Set.image_congr fun p _ => suppMap_tr hS hne c t p

lemma QminusS_tr (hS : IsCompact S) (hne : S.Nonempty) (c : ℝ²) (t : ℝ) :
    QminusS (tr c S) t = tr c (QminusS S t) := by
  rw [← suppMap_image_Qminus, ← suppMap_image_Qminus]
  show _ = (· + c) '' (suppMap S t '' Qminus)
  rw [Set.image_image]
  exact Set.image_congr fun p _ => suppMap_tr hS hne c t p

lemma strips_tr (hS : IsCompact S) (hne : S.Nonempty) (c : ℝ²) (ω : ℝ) :
    strips (tr c S) ω = tr c (strips S ω) := by
  unfold strips
  simp only [tr_inter, tr_hpLe, tr_hpGe, supportFn_tr hS hne]
  congr 3 <;> ring

lemma monotoneHull_tr (hS : IsCompact S) (hne : S.Nonempty) (c : ℝ²) (ω : ℝ) :
    monotoneHull (tr c S) ω = tr c (monotoneHull S ω) := by
  ext p
  simp only [monotoneHull, strips_tr hS hne, suppHallway_tr hS hne, Set.mem_inter_iff,
    Set.mem_iInter₂, mem_tr]

/-! ## Standard position -/

/-- **Def 2.3.4.** `S` is in standard position for the rotation angle `ω`. -/
def StdPos (S : Set ℝ²) (ω : ℝ) : Prop := supportFn S ω = 1 ∧ supportFn S (π / 2) = 1

/-- The translation vector putting `S` in standard position (for `ω ∈ (0, π/2]`). -/
def stdVec (S : Set ℝ²) (ω : ℝ) : ℝ² :=
  pt ((1 - supportFn S ω - (1 - supportFn S (π / 2)) * sin ω) / cos ω) (1 - supportFn S (π / 2))

/-- **Prop 2.3.1 (existence).** -/
lemma stdPos_tr_stdVec (hS : IsCompact S) (hne : S.Nonempty) (hω0 : 0 < ω) (hω1 : ω ≤ π / 2) :
    StdPos (tr (stdVec S ω) S) ω := by
  constructor
  · rw [supportFn_tr hS hne, inner_eq, stdVec, pt_zero, pt_one, u_coord_zero, u_coord_one]
    rcases hω1.lt_or_eq with h | h
    · have hc : cos ω ≠ 0 := (cos_pos_of_mem_Ioo ⟨by linarith, h⟩).ne'
      field_simp
      ring
    · subst h
      simp only [cos_pi_div_two, sin_pi_div_two, div_zero, zero_mul, mul_one, zero_add]
      ring
  · rw [supportFn_tr hS hne, inner_u_pi_div_two, stdVec, pt_one]
    ring

/-- In standard position the strips of Fable's `monotoneHull` are Baek's `P_ω = H ∩ V_ω`. -/
lemma strips_of_stdPos (h : StdPos S ω) : strips S ω = para ω := by
  ext p
  simp only [strips, para, Hstrip, Vstrip, h.1, h.2, hpLe, hpGe, Set.mem_inter_iff,
    Set.mem_ofPred_eq, inner_u_pi_div_two, sub_self]
  tauto

/-! ## Baek's moving sofas with a rotation angle -/

/-- **Def 1.1.2 + Def 2.3.3.** Some translate of `S` is an upstream moving sofa whose motion has a
continuous rotation angle `θ` (`θ 0 = 0`) ending at `θ 1 = -ω`, i.e. the sofa turns *clockwise*
by `ω`. -/
def IsSofaWithAngle (S : Set ℝ²) (ω : ℝ) : Prop :=
  ∃ (c : ℝ²) (m : I → E(2)) (θ : I → ℝ), IsMovingSofa (tr c S) m ∧ Continuous θ ∧ θ 0 = 0 ∧
    (∀ t p, m t p = rot (θ t) p + m t 0) ∧ θ 1 = -ω

/-- Every upstream moving sofa is a Baek sofa, with the angle of its (unique) continuous lift. -/
lemma isSofaWithAngle_of_isMovingSofa {s : Set ℝ²} {m : I → E(2)} (hm : IsMovingSofa s m) :
    ∃ ω, IsSofaWithAngle s ω := by
  obtain ⟨θ, hθc, hθ0, hθ⟩ := exists_rotationAngle hm.continuous hm.zero
  exact ⟨-θ 1, 0, m, θ, by rwa [tr_zero], hθc, hθ0, hθ, by ring⟩

namespace IsSofaWithAngle

lemma tr' (h : IsSofaWithAngle S ω) (d : ℝ²) : IsSofaWithAngle (tr d S) ω := by
  obtain ⟨c, m, θ, hm, hθc, hθ0, hθ, hθ1⟩ := h
  refine ⟨c - d, m, θ, ?_, hθc, hθ0, hθ, hθ1⟩
  rwa [tr_tr, show d + (c - d) = c by abel]

lemma isCompact (h : IsSofaWithAngle S ω) : IsCompact S := by
  obtain ⟨c, m, θ, hm, -⟩ := h
  simpa [tr_neg_tr] using isCompact_tr hm.isCompact (-c)

lemma isConnected (h : IsSofaWithAngle S ω) : IsConnected S := by
  obtain ⟨c, m, θ, hm, -⟩ := h
  simpa [tr_neg_tr] using isConnected_tr hm.isConnected (-c)

lemma isClosed (h : IsSofaWithAngle S ω) : IsClosed S := by
  obtain ⟨c, m, θ, hm, -⟩ := h
  simpa [tr_neg_tr] using isClosed_tr hm.isClosed (-c)

lemma nonempty (h : IsSofaWithAngle S ω) : S.Nonempty := h.isConnected.nonempty

/-- **Prop 1.2.2 (via Fable's normalisation-free hull).** -/
lemma subset_monotoneHull (h : IsSofaWithAngle S ω) : S ⊆ monotoneHull S ω := by
  have hS := h.isCompact
  have hne := h.nonempty
  obtain ⟨c, m, θ, hm, hθc, hθ0, hθ, hθ1⟩ := h
  have h1 := hm.subset_monotoneHull hθc hθ0 hθ hθ1
  have h2 := tr_mono (c := -c) h1
  rwa [tr_neg_tr, monotoneHull_tr hS hne, tr_neg_tr] at h2

/-- **Prop 1.2.2.** A moving sofa with rotation angle `ω` in standard position lies in `P_ω` and
in every supporting hallway `L_S(t)`, `t ∈ [0, ω]`. -/
theorem subset (h : IsSofaWithAngle S ω) (hstd : StdPos S ω) :
    S ⊆ para ω ∧ ∀ t ∈ Icc (0 : ℝ) ω, S ⊆ suppHallway S t := by
  have hsub := h.subset_monotoneHull
  refine ⟨fun p hp => ?_, fun t ht p hp => ?_⟩
  · have := (hsub hp).1
    rwa [strips_of_stdPos hstd] at this
  · exact monotoneHull_subset_suppHallway S ht (hsub hp)

end IsSofaWithAngle

end Sofa
