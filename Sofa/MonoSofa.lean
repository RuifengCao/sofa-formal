/-
# Sofa/MonoSofa.lean — the monotone sofa `I(S)` and the convex set `C(S)` (Baek §2.3)

* `Jω`, `Imono S ω = I(S)` (Def 2.3.6), `Ccap S ω = C(S)` (Def 2.3.10), `ClosedDir` (Def 2.3.8);
* Prop 2.3.3 / 2.3.4 (`S ⊆ I(S) ⊆ C(S)`), Lemma 2.3.5 (support functions agree on `J_ω`);
* **Thm 2.3.6** (`I(S)` is connected);
* the supporting-hallway movement (`isSofaWithAngle_of_subset_suppHallway`), used for
  **Thm 2.3.2** (`I(S)` is a moving sofa with the same rotation angle, in standard position)
  and later for Thm 2.5.9.

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 1 (2026-09-17, Opus 5), no `sorry`.
-/
import Sofa.StdPos
import Sofa.SupportLipschitz

noncomputable section

open Real Set MovingSofa
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa

variable {S : Set ℝ²} {ω : ℝ}

/-! ## Definitions -/

/-- **Def 2.3.11.** `J_ω = [0, ω] ∪ [π/2, ω + π/2]`. -/
def Jω (ω : ℝ) : Set ℝ := Icc 0 ω ∪ Icc (π / 2) (ω + π / 2)

lemma mem_Jω_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ω) : t ∈ Jω ω := Or.inl ht

lemma add_pi_div_two_mem_Jω {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ω) : t + π / 2 ∈ Jω ω :=
  Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- **Def 2.3.6.** The monotone hull `I(S) = P_ω ∩ ⋂_{t ∈ [0, ω]} L_S(t)`. -/
def Imono (S : Set ℝ²) (ω : ℝ) : Set ℝ² := para ω ∩ ⋂ t ∈ Icc (0 : ℝ) ω, suppHallway S t

/-- **Def 2.3.10.** `C(S) = P_ω ∩ ⋂_{t ∈ [0, ω]} Q⁺_S(t)`. -/
def Ccap (S : Set ℝ²) (ω : ℝ) : Set ℝ² := para ω ∩ ⋂ t ∈ Icc (0 : ℝ) ω, QplusS S t

/-- **Def 2.3.7.** A monotone sofa with rotation angle `ω`. -/
def IsMonotoneSofa (T : Set ℝ²) (ω : ℝ) : Prop :=
  ∃ S, IsSofaWithAngle S ω ∧ StdPos S ω ∧ T = Imono S ω

/-- **Def 2.3.8.** `X` is closed in the direction of `w`. -/
def ClosedDir (X : Set ℝ²) (w : ℝ²) : Prop := ∀ x ∈ X, ∀ r : ℝ, 0 ≤ r → x + r • w ∈ X

lemma Imono_eq_monotoneHull (h : StdPos S ω) : Imono S ω = monotoneHull S ω := by
  rw [Imono, monotoneHull, strips_of_stdPos h]

lemma suppHallway_subset_QplusS (S : Set ℝ²) (t : ℝ) : suppHallway S t ⊆ QplusS S t := by
  rw [suppHallway_eq]; exact sdiff_subset

lemma Imono_subset_Ccap (S : Set ℝ²) (ω : ℝ) : Imono S ω ⊆ Ccap S ω :=
  inter_subset_inter_right _ (iInter₂_mono fun t _ => suppHallway_subset_QplusS S t)

lemma mem_Imono_iff {p : ℝ²} :
    p ∈ Imono S ω ↔ p ∈ para ω ∧ ∀ t ∈ Icc (0 : ℝ) ω, p ∈ suppHallway S t := by
  simp only [Imono, mem_inter_iff, mem_iInter₂]

lemma mem_Ccap_iff {p : ℝ²} :
    p ∈ Ccap S ω ↔ p ∈ para ω ∧ ∀ t ∈ Icc (0 : ℝ) ω, p ∈ QplusS S t := by
  simp only [Ccap, mem_inter_iff, mem_iInter₂]

/-- **Prop 2.3.3.** -/
lemma IsSofaWithAngle.subset_Imono (h : IsSofaWithAngle S ω) (hstd : StdPos S ω) :
    S ⊆ Imono S ω := by
  intro p hp
  obtain ⟨h1, h2⟩ := h.subset hstd
  exact mem_Imono_iff.2 ⟨h1 hp, fun t ht => h2 t ht hp⟩

/-- Points of `C(S)` lie below the supporting lines with normal angles in `J_ω`. -/
lemma inner_le_of_mem_Ccap {p : ℝ²} (hp : p ∈ Ccap S ω) {t : ℝ} (ht : t ∈ Jω ω) :
    ⟪p, u t⟫ ≤ supportFn S t := by
  have hq := (mem_Ccap_iff.1 hp).2
  rcases ht with ht | ht
  · exact (hq t ht).1
  · have := (hq (t - π / 2) ⟨by linarith [ht.1], by linarith [ht.2]⟩).2
    rwa [sub_add_cancel] at this

/-! ## Compactness -/

lemma norm_le_add_of_abs_coord_le {p : ℝ²} {a b : ℝ} (h0 : |p 0| ≤ a) (h1 : |p 1| ≤ b) :
    ‖p‖ ≤ a + b := by
  have ha : 0 ≤ a := (abs_nonneg _).trans h0
  have hb : 0 ≤ b := (abs_nonneg _).trans h1
  have hn2 : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have e0 : p 0 ^ 2 ≤ a ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have e1 : p 1 ^ 2 ≤ b ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  rw [← sq_le_sq₀ (norm_nonneg p) (by positivity)]
  nlinarith [mul_nonneg ha hb]

lemma isClosed_para (ω : ℝ) : IsClosed (para ω) := isClosed_Hstrip.inter (isClosed_Vstrip ω)

lemma convex_para (ω : ℝ) : Convex ℝ (para ω) := convex_Hstrip.inter (convex_Vstrip ω)

lemma convex_QplusS (S : Set ℝ²) (t : ℝ) : Convex ℝ (QplusS S t) :=
  (convex_hpLe _ _).inter (convex_hpLe _ _)

lemma isClosed_Ccap (S : Set ℝ²) (ω : ℝ) : IsClosed (Ccap S ω) :=
  (isClosed_para ω).inter (isClosed_biInter fun t _ => isClosed_QplusS S t)

lemma isClosed_Imono (S : Set ℝ²) (ω : ℝ) : IsClosed (Imono S ω) :=
  (isClosed_para ω).inter (isClosed_biInter fun t _ => isClosed_suppHallway S t)

lemma convex_Ccap (S : Set ℝ²) (ω : ℝ) : Convex ℝ (Ccap S ω) :=
  (convex_para ω).inter (convex_iInter₂ fun t _ => convex_QplusS S t)

lemma isBounded_Ccap (hω0 : 0 < ω) (hω1 : ω ≤ π / 2) : Bornology.IsBounded (Ccap S ω) := by
  have hs : 0 < sin ω := sin_pos_of_pos_of_lt_pi hω0 (by linarith [pi_pos])
  have hc : 0 ≤ cos ω := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hω1⟩
  refine isBounded_iff_forall_norm_le.2
    ⟨(|supportFn S 0| + |supportFn S (ω + π / 2)| / sin ω) + 1, fun p hp => ?_⟩
  have hH : 0 ≤ p 1 ∧ p 1 ≤ 1 := hp.1.1
  have h0 := inner_le_of_mem_Ccap hp (t := 0) (Or.inl ⟨le_rfl, hω0.le⟩)
  have h1 := inner_le_of_mem_Ccap hp (t := ω + π / 2) (Or.inr ⟨by linarith, le_rfl⟩)
  rw [inner_u_zero] at h0
  rw [u_add_pi_div_two, inner_eq, v_coord_zero, v_coord_one] at h1
  refine norm_le_add_of_abs_coord_le ?_ (abs_le.2 ⟨by linarith [hH.1], hH.2⟩)
  have hA := le_abs_self (supportFn S 0)
  have hB := le_abs_self (supportFn S (ω + π / 2))
  have hC := div_nonneg (abs_nonneg (supportFn S (ω + π / 2))) hs.le
  have hD := abs_nonneg (supportFn S 0)
  rw [abs_le]
  constructor
  · have e1 : -|supportFn S (ω + π / 2)| ≤ p 0 * sin ω := by
      nlinarith [mul_nonneg hH.1 hc]
    have e2 : -|supportFn S (ω + π / 2)| / sin ω ≤ p 0 := by
      rw [div_le_iff₀ hs]; exact e1
    rw [neg_div] at e2
    linarith
  · linarith

lemma isCompact_Ccap (hω0 : 0 < ω) (hω1 : ω ≤ π / 2) : IsCompact (Ccap S ω) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_Ccap S ω) (isBounded_Ccap hω0 hω1)

lemma isCompact_Imono (hω0 : 0 < ω) (hω1 : ω ≤ π / 2) : IsCompact (Imono S ω) :=
  (isCompact_Ccap hω0 hω1).of_isClosed_subset (isClosed_Imono S ω) (Imono_subset_Ccap S ω)

/-! ## Lemma 2.3.5 -/

/-- **Lemma 2.3.5.** If `S ⊆ X ⊆ C(S)` with `X` compact, then `h_X = h_S` on `J_ω`. -/
lemma supportFn_eq_of_subset_Ccap {X : Set ℝ²} (hX : IsCompact X) (hne : S.Nonempty)
    (hSX : S ⊆ X) (hXC : X ⊆ Ccap S ω) {t : ℝ} (ht : t ∈ Jω ω) :
    supportFn X t = supportFn S t := by
  apply le_antisymm
  · rw [supportFn_le_iff hX (hne.mono hSX)]
    intro p hp
    exact inner_le_of_mem_Ccap (hXC hp) ht
  · exact supportFn_mono hX hne hSX t

lemma suppMap_congr {T : Set ℝ²} {t : ℝ} (h1 : supportFn S t = supportFn T t)
    (h2 : supportFn S (t + π / 2) = supportFn T (t + π / 2)) : suppMap S t = suppMap T t := by
  funext p; simp only [suppMap, h1, h2]

lemma suppHallway_congr {T : Set ℝ²} {t : ℝ} (h1 : supportFn S t = supportFn T t)
    (h2 : supportFn S (t + π / 2) = supportFn T (t + π / 2)) :
    suppHallway S t = suppHallway T t := by
  simp only [suppHallway, suppMap_congr h1 h2]

lemma QplusS_congr {T : Set ℝ²} {t : ℝ} (h1 : supportFn S t = supportFn T t)
    (h2 : supportFn S (t + π / 2) = supportFn T (t + π / 2)) : QplusS S t = QplusS T t := by
  simp only [QplusS, h1, h2]

lemma QminusS_congr {T : Set ℝ²} {t : ℝ} (h1 : supportFn S t = supportFn T t)
    (h2 : supportFn S (t + π / 2) = supportFn T (t + π / 2)) : QminusS S t = QminusS T t := by
  simp only [QminusS, h1, h2]

/-- `C(S)` and `I(S)` only depend on `h_S` restricted to `J_ω`. -/
lemma Ccap_congr {T : Set ℝ²} (h : ∀ t ∈ Jω ω, supportFn S t = supportFn T t) :
    Ccap S ω = Ccap T ω := by
  ext p
  simp only [mem_Ccap_iff]
  refine and_congr_right fun _ => forall₂_congr fun t ht => ?_
  rw [QplusS_congr (h t (mem_Jω_of_mem_Icc ht)) (h _ (add_pi_div_two_mem_Jω ht))]

lemma Imono_congr {T : Set ℝ²} (h : ∀ t ∈ Jω ω, supportFn S t = supportFn T t) :
    Imono S ω = Imono T ω := by
  ext p
  simp only [mem_Imono_iff]
  refine and_congr_right fun _ => forall₂_congr fun t ht => ?_
  rw [suppHallway_congr (h t (mem_Jω_of_mem_Icc ht)) (h _ (add_pi_div_two_mem_Jω ht))]

/-! ## Closedness in a direction -/

lemma closedDir_QminusS {t : ℝ} {w : ℝ²} (h1 : ⟪w, u t⟫ ≤ 0) (h2 : ⟪w, v t⟫ ≤ 0) :
    ClosedDir (QminusS S t) w := by
  intro x hx r hr
  rw [mem_QminusS_iff] at hx ⊢
  rw [u_add_pi_div_two] at hx ⊢
  rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  constructor
  · nlinarith [mul_nonneg hr (neg_nonneg.2 h1)]
  · nlinarith [mul_nonneg hr (neg_nonneg.2 h2)]

/-- For `θ ∈ [ω, π/2]` and `t ∈ [0, ω]`, `Q⁻_S(t)` is closed in the direction `-u_θ`. -/
lemma closedDir_QminusS_neg_u {t θ : ℝ} (ht : t ∈ Icc (0 : ℝ) ω) (hθ : θ ∈ Icc ω (π / 2)) :
    ClosedDir (QminusS S t) (-u θ) := by
  have h0 : 0 ≤ θ - t := by linarith [ht.2, hθ.1]
  have h1 : θ - t ≤ π / 2 := by linarith [ht.1, hθ.2]
  apply closedDir_QminusS
  · rw [inner_neg_left, inner_u_u_eq_cos, neg_nonpos]
    exact cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], h1⟩
  · rw [inner_neg_left, inner_u_v_eq_sin, neg_nonpos]
    exact sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [pi_pos])

/-! ## Theorem 2.3.6 -/

lemma v_pi_div_two : v (π / 2) = -u 0 := by
  ext i; fin_cases i <;> simp [u, v]

/-- The two open sectors at `p` cut out by the lines through `p` with directions `u_θ`,
`θ ∈ [ω, π/2]`: every point outside both sectors lies on one of these lines (IVT). -/
lemma exists_line_of_not_mem_sectors {p q : ℝ²} (hω1 : ω ≤ π / 2)
    (hR : ¬ (0 < ⟪q - p, u 0⟫ ∧ ⟪q - p, v ω⟫ < 0))
    (hL : ¬ (⟪q - p, u 0⟫ < 0 ∧ 0 < ⟪q - p, v ω⟫)) :
    ∃ θ ∈ Icc ω (π / 2), ⟪q - p, v θ⟫ = 0 := by
  set g : ℝ → ℝ := fun θ => ⟪q - p, v θ⟫ with hg
  have hgc : Continuous g := continuous_const.inner continuous_v
  have hg0 : g ω = ⟪q - p, v ω⟫ := rfl
  have hg1 : g (π / 2) = -⟪q - p, u 0⟫ := by
    simp only [hg, v_pi_div_two, inner_neg_right]
  have hmem : (0 : ℝ) ∈ uIcc (g ω) (g (π / 2)) := by
    rw [hg0, hg1, mem_uIcc]
    set A := ⟪q - p, u 0⟫
    set B := ⟪q - p, v ω⟫
    rcases le_total B 0 with hB | hB <;> rcases le_total A 0 with hA | hA
    · exact Or.inl ⟨hB, by linarith⟩
    · rcases hB.lt_or_eq with hB' | hB'
      · rcases hA.lt_or_eq with hA' | hA'
        · exact absurd ⟨hA', hB'⟩ hR
        · exact Or.inl ⟨hB, by linarith⟩
      · exact Or.inr ⟨by linarith, hB'.ge⟩
    · rcases hB.lt_or_eq with hB' | hB'
      · rcases hA.lt_or_eq with hA' | hA'
        · exact absurd ⟨hA', hB'⟩ hL
        · exact Or.inr ⟨by linarith, hB⟩
      · exact Or.inl ⟨hB'.ge, by linarith⟩
    · exact Or.inr ⟨by linarith, hB⟩
  obtain ⟨θ, hθ, hθ0⟩ := intermediate_value_uIcc hgc.continuousOn hmem
  rw [uIcc_of_le hω1] at hθ
  exact ⟨θ, hθ, hθ0⟩

/-- **Theorem 2.3.6.** `I(S)` is connected. -/
theorem isConnected_Imono (hS : IsCompact S) (hconn : IsConnected S) (hω0 : 0 < ω)
    (hω1 : ω ≤ π / 2) (hsub : S ⊆ Imono S ω) : IsConnected (Imono S ω) := by
  have hne := hconn.nonempty
  obtain ⟨x₀, hx₀⟩ := hne
  refine ⟨⟨x₀, hsub hx₀⟩, isPreconnected_of_forall x₀ fun p hp => ?_⟩
  -- Step 1: a line through `p` with direction `u_θ`, `θ ∈ [ω, π/2]`, meets `S`.
  obtain ⟨θ, hθ, q, hq, hpq⟩ : ∃ θ ∈ Icc ω (π / 2), ∃ q ∈ S, ⟪q - p, v θ⟫ = 0 := by
    by_contra hcon
    push Not at hcon
    set UR : Set ℝ² := {q | 0 < ⟪q - p, u 0⟫ ∧ ⟪q - p, v ω⟫ < 0} with hUR
    set UL : Set ℝ² := {q | ⟪q - p, u 0⟫ < 0 ∧ 0 < ⟪q - p, v ω⟫} with hUL
    have hc0 : Continuous fun q : ℝ² => ⟪q - p, u 0⟫ :=
      (continuous_id.sub continuous_const).inner continuous_const
    have hc1 : Continuous fun q : ℝ² => ⟪q - p, v ω⟫ :=
      (continuous_id.sub continuous_const).inner continuous_const
    have hURo : IsOpen UR := (isOpen_lt continuous_const hc0).inter (isOpen_lt hc1 continuous_const)
    have hULo : IsOpen UL := (isOpen_lt hc0 continuous_const).inter (isOpen_lt continuous_const hc1)
    have hdisj : Disjoint UR UL := by
      rw [Set.disjoint_left]
      rintro q ⟨h1, -⟩ ⟨h2, -⟩
      linarith
    have hcover : S ⊆ UR ∪ UL := by
      intro q hq
      by_contra hn
      simp only [mem_union, hUR, hUL, mem_ofPred_eq] at hn
      push Not at hn
      obtain ⟨θ, hθ, h0⟩ := exists_line_of_not_mem_sectors hω1
        (fun h => absurd h.2 (not_lt.2 (hn.1 h.1)))
        (fun h => absurd h.2 (not_lt.2 (hn.2 h.1)))
      exact hcon θ hθ q hq h0
    -- the edge points of `S` at angles `0` and `ω + π/2`
    have hpC := Imono_subset_Ccap S ω hp
    obtain ⟨e, he, he0⟩ := exists_supportFn_eq hS ⟨x₀, hx₀⟩ 0
    obtain ⟨f, hf, hf0⟩ := exists_supportFn_eq hS ⟨x₀, hx₀⟩ (ω + π / 2)
    have hpe : ⟪p, u 0⟫ ≤ ⟪e, u 0⟫ := by
      rw [he0]; exact inner_le_of_mem_Ccap hpC (Or.inl ⟨le_rfl, hω0.le⟩)
    have hpf : ⟪p, u (ω + π / 2)⟫ ≤ ⟪f, u (ω + π / 2)⟫ := by
      rw [hf0]; exact inner_le_of_mem_Ccap hpC (Or.inr ⟨by linarith, le_rfl⟩)
    rw [u_add_pi_div_two] at hpf
    have heL : e ∉ UL := by
      rintro ⟨h1, -⟩
      rw [inner_sub_left] at h1
      linarith
    have hfR : f ∉ UR := by
      rintro ⟨-, h2⟩
      rw [inner_sub_left] at h2
      linarith
    rcases hconn.isPreconnected.subset_or_subset hURo hULo hdisj hcover with h | h
    · exact hfR (h hf)
    · exact heL (h he)
  -- Step 2: the segment `[p, q]` lies in `I(S)`.
  have hqI := hsub hq
  have hseg : segment ℝ p q ⊆ Imono S ω := by
    intro z hz
    have hzP : z ∈ para ω := (convex_para ω).segment_subset (mem_Imono_iff.1 hp).1
      (mem_Imono_iff.1 hqI).1 hz
    refine mem_Imono_iff.2 ⟨hzP, fun t ht => ?_⟩
    have hpt := (mem_Imono_iff.1 hp).2 t ht
    have hqt := (mem_Imono_iff.1 hqI).2 t ht
    rw [suppHallway_eq] at hpt hqt ⊢
    refine ⟨(convex_QplusS S t).segment_subset hpt.1 hqt.1 hz, fun hzm => ?_⟩
    -- `q - p = μ u_θ`
    have hdec := decomp_u_v θ (q - p)
    rw [hpq, zero_smul, add_zero] at hdec
    set μ := ⟪q - p, u θ⟫ with hμ
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    have hzp : a • p + b • q = p + b • (q - p) := by
      rw [show a = 1 - b by linarith]; module
    have hzq : a • p + b • q = q + a • (p - q) := by
      rw [show b = 1 - a by linarith]; module
    have hclosed := closedDir_QminusS_neg_u (S := S) ht hθ
    rcases le_total 0 μ with hμ0 | hμ0
    · -- `p = z + (b μ) (-u_θ)`
      have : p = (a • p + b • q) + (b * μ) • (-u θ) := by
        rw [hzp, hdec]
        module
      exact hpt.2 (this ▸ hclosed _ hzm _ (mul_nonneg hb hμ0))
    · -- `q = z + (a (-μ)) (-u_θ)`
      have : q = (a • p + b • q) + (a * -μ) • (-u θ) := by
        rw [hzq, show p - q = -(q - p) by abel, hdec]
        module
      exact hqt.2 (this ▸ hclosed _ hzm _ (mul_nonneg ha (neg_nonneg.2 hμ0)))
  refine ⟨S ∪ segment ℝ p q, union_subset hsub hseg, Or.inl hx₀,
    Or.inr (left_mem_segment ℝ p q), ?_⟩
  exact IsPreconnected.union q hq (right_mem_segment ℝ p q) hconn.isPreconnected
    (convex_segment p q).isPreconnected

/-! ## The supporting-hallway movement -/

/-- The motion of the supporting hallways of `S` seen from `L`, starting at the identity:
at time `τ` it maps `f_{S,0}(p)` to `f_{S,ωτ}⁻¹(f_{S,0}(p))`. -/
def suppMotion (S : Set ℝ²) (ω : ℝ) (τ : I) : E(2) :=
  rotateTranslate ((-(ω * (τ : ℝ)) : ℝ) : Real.Angle)
    (innerCorner S 0 - innerCorner S (ω * (τ : ℝ)))

lemma suppMotion_apply (τ : I) (p : ℝ²) :
    suppMotion S ω τ p = suppMapInv S (ω * (τ : ℝ)) (p + innerCorner S 0) := by
  rw [suppMotion, rotateTranslate_apply_eq_rot, suppMapInv]
  congr 1; abel

lemma suppMapInv_suppMap (t : ℝ) (p : ℝ²) : suppMapInv S t (suppMap S t p) = p :=
  suppMap_injective S t (suppMap_suppMapInv S t _)

lemma suppMapInv_mem_hallway {t : ℝ} {r : ℝ²} (hr : r ∈ suppHallway S t) :
    suppMapInv S t r ∈ hallway := by
  obtain ⟨w, hw, rfl⟩ := hr
  rw [suppMapInv_suppMap, hallway_eq_diff]; exact hw

lemma continuous_innerCorner (hS : IsCompact S) (hne : S.Nonempty) :
    Continuous (innerCorner S) := by
  have hh := continuous_supportFn hS hne
  unfold innerCorner
  exact ((hh.sub continuous_const).smul continuous_u).add
    (((hh.comp (continuous_id.add continuous_const)).sub continuous_const).smul continuous_v)

lemma inner_innerCorner_u (t : ℝ) : ⟪innerCorner S t, u t⟫ = supportFn S t - 1 := by
  rw [innerCorner, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u,
    inner_v_u]; ring

lemma innerCorner_zero_of_stdPos (h : StdPos S ω) : innerCorner S 0 = pt (supportFn S 0 - 1) 0 := by
  rw [innerCorner, zero_add, h.2, sub_self, zero_smul, add_zero]
  ext i; fin_cases i <;> simp [u, pt, e₀, e₁]

lemma mem_horizontalHallway_of_mem_hallway {p : ℝ²} (h : p ∈ hallway) (h0 : 0 ≤ p 1)
    (h1 : p 1 ≤ 1) : p ∈ horizontalHallway := by
  rw [hallway_eq_diff] at h
  exact (mem_horizontalHallway_iff p).2 ⟨h.1.1, h0, h1⟩

lemma mem_verticalHallway_of_mem_hallway {p : ℝ²} (h : p ∈ hallway) (h0 : 0 ≤ p 0)
    (h1 : p 0 ≤ 1) : p ∈ verticalHallway := by
  rw [hallway_eq_diff] at h
  exact (mem_verticalHallway_iff p).2 ⟨h0, h1, h.1.2⟩

/-- **The supporting-hallway movement.**  If `T` is a closed connected subset of `P_ω` contained
in every supporting hallway `L_S(t)`, `t ∈ [0, ω]`, of a compact `S` in standard position, then `T`
is a moving sofa with rotation angle `ω`. -/
theorem isSofaWithAngle_of_subset_suppHallway {T : Set ℝ²} (hS : IsCompact S)
    (hne : S.Nonempty) (hω0 : 0 ≤ ω) (hstd : StdPos S ω) (hT : IsConnected T)
    (hTc : IsClosed T) (hTP : T ⊆ para ω) (hTL : ∀ t ∈ Icc (0 : ℝ) ω, T ⊆ suppHallway S t) :
    IsSofaWithAngle T ω := by
  have hτ : ∀ τ : I, ω * (τ : ℝ) ∈ Icc (0 : ℝ) ω := fun τ =>
    ⟨mul_nonneg hω0 τ.2.1, mul_le_of_le_one_right hω0 τ.2.2⟩
  -- the motion acts on `tr (-x_S(0)) T` as `r - x_S(0) ↦ f_{S,ωτ}⁻¹ r`
  have hact : ∀ τ : I, ∀ r : ℝ², suppMotion S ω τ (r + -innerCorner S 0) =
      suppMapInv S (ω * (τ : ℝ)) r := by
    intro τ r; rw [suppMotion_apply, neg_add_cancel_right]
  refine ⟨-innerCorner S 0, suppMotion S ω, fun τ => -(ω * (τ : ℝ)), ⟨isConnected_tr hT _,
    isClosed_tr hTc _, ?_, ?_, ?_, ?_, ?_⟩, by fun_prop, by simp, ?_, by simp⟩
  · -- continuity
    refine continuous_motion_of_continuous_apply fun q => ?_
    simp only [suppMotion_apply, suppMapInv]
    have hτc : Continuous fun τ : I => ω * (τ : ℝ) := by fun_prop
    exact continuous_rot_apply hτc.neg
      (continuous_const.sub ((continuous_innerCorner hS hne).comp hτc))
  · -- `m 0 = id`
    ext q : 1
    rw [suppMotion_apply]
    simp only [Set.Icc.coe_zero, mul_zero, suppMapInv, neg_zero, rot_zero,
      AffineIsometryEquiv.coe_refl, id]
    abel
  · -- initial position
    rintro _ ⟨r, hr, rfl⟩
    have hL := suppMapInv_mem_hallway (hTL 0 ⟨le_rfl, hω0⟩ hr)
    have e : suppMapInv S 0 r = r + -innerCorner S 0 := by
      rw [suppMapInv, neg_zero, rot_zero, sub_eq_add_neg]
    rw [e] at hL
    have hH : 0 ≤ r 1 ∧ r 1 ≤ 1 := (hTP hr).1
    have hc1 : (r + -innerCorner S 0) 1 = r 1 := by
      rw [innerCorner_zero_of_stdPos hstd]; simp
    exact mem_horizontalHallway_of_mem_hallway hL (by rw [hc1]; exact hH.1)
      (by rw [hc1]; exact hH.2)
  · -- inside the hallway
    rintro τ _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    rw [hact]
    exact suppMapInv_mem_hallway (hTL _ (hτ τ) hr)
  · -- final position
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    rw [hact, Set.Icc.coe_one, mul_one]
    have hL := suppMapInv_mem_hallway (hTL ω ⟨hω0, le_rfl⟩ hr)
    have hV : 0 ≤ ⟪r, u ω⟫ ∧ ⟪r, u ω⟫ ≤ 1 := (hTP hr).2
    have e : suppMapInv S ω r 0 = ⟪r, u ω⟫ := by
      rw [suppMapInv, rot_neg_coord_zero, inner_sub_left, inner_innerCorner_u, hstd.1]
      ring
    exact mem_verticalHallway_of_mem_hallway hL (by rw [e]; exact hV.1) (by rw [e]; exact hV.2)
  · -- the rotation angle
    intro τ p
    rw [suppMotion_apply, suppMotion_apply, suppMapInv, suppMapInv, zero_add, ← rot_add]
    congr 1; abel

/-! ## Theorem 2.3.2 -/

/-- **Theorem 2.3.2.** For a moving sofa `S` with rotation angle `ω ∈ (0, π/2]` in standard
position, `I(S)` is a moving sofa with the same rotation angle, in standard position, and
contains `S`. -/
theorem IsSofaWithAngle.Imono_props (h : IsSofaWithAngle S ω) (hstd : StdPos S ω) (hω0 : 0 < ω)
    (hω1 : ω ≤ π / 2) :
    IsSofaWithAngle (Imono S ω) ω ∧ StdPos (Imono S ω) ω ∧ S ⊆ Imono S ω := by
  have hS := h.isCompact
  have hne := h.nonempty
  have hsub := h.subset_Imono hstd
  have hI := isCompact_Imono (S := S) hω0 hω1
  refine ⟨isSofaWithAngle_of_subset_suppHallway hS hne hω0.le hstd
      (isConnected_Imono hS h.isConnected hω0 hω1 hsub) (isClosed_Imono S ω)
      (fun p hp => (mem_Imono_iff.1 hp).1) (fun t ht p hp => (mem_Imono_iff.1 hp).2 t ht),
    ⟨?_, ?_⟩, hsub⟩
  · rw [supportFn_eq_of_subset_Ccap hI hne hsub (Imono_subset_Ccap S ω)
      (Or.inl ⟨hω0.le, le_rfl⟩), hstd.1]
  · rw [supportFn_eq_of_subset_Ccap hI hne hsub (Imono_subset_Ccap S ω)
      (Or.inr ⟨le_rfl, by linarith⟩), hstd.2]

/-- A monotone sofa is a moving sofa. -/
lemma IsMonotoneSofa.isSofaWithAngle {T : Set ℝ²} (h : IsMonotoneSofa T ω) (hω0 : 0 < ω)
    (hω1 : ω ≤ π / 2) : IsSofaWithAngle T ω := by
  obtain ⟨S, hS, hstd, rfl⟩ := h
  exact (hS.Imono_props hstd hω0 hω1).1

end Sofa
