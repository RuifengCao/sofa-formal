/-
# Sofa/Hausdorff.lean — Hausdorff convergence of planar convex bodies (M3a)

* `abs_supportFn_sub_le_hausdorffDist`: `|h_S(t) - h_T(t)| ≤ d_H(S, T)` (half of Schneider
  Lemma 1.8.14; this is the direction used in Baek Thm 3.4.3, 3.5.4, 3.5.5, Lemma 4.1.1);
* **Lemma 3.5.3** (`subset_of_tendsto_hausdorffDist`);
* Hausdorff limits of convex sets are convex; **Blaschke selection theorem**
  (`exists_tendsto_hausdorffDist`), via Mathlib's compactness of `NonemptyCompacts` in the
  Vietoris (= Hausdorff metric) topology;
* the nearest-point variational inequality, and: a point whose `δ`-ball lies in `K` belongs to
  every convex compact `T` with `d_H(K, T) < δ` (the key step of lower semicontinuity of area).

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 1 (2026-09-17, Opus 5): compiled in the cloud dev tree
(Lean 4.33.1, Mathlib v4.33.1 with subset imports), no `sorry`; full `import Mathlib` re-check pending.
-/
import Mathlib.Topology.Sets.VietorisTopology
import Mathlib.Topology.MetricSpace.Closeds
import Sofa.Support

noncomputable section

open Real Set Filter Topology Metric
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

/-! ## Support functions are 1-Lipschitz in the Hausdorff distance -/

lemma hausdorffEDist_ne_top_of_isCompact {S T : Set ℝ²} (hS : IsCompact S) (hT : IsCompact T)
    (hSne : S.Nonempty) (hTne : T.Nonempty) : hausdorffEDist S T ≠ ⊤ :=
  hausdorffEDist_ne_top_of_nonempty_of_bounded hSne hTne hS.isBounded hT.isBounded

lemma supportFn_le_add_hausdorffDist {S T : Set ℝ²} (hS : IsCompact S) (hT : IsCompact T)
    (hSne : S.Nonempty) (hTne : T.Nonempty) (t : ℝ) :
    supportFn S t ≤ supportFn T t + hausdorffDist S T := by
  rw [supportFn_le_iff hS hSne]
  intro p hp
  obtain ⟨q, hq, hpq⟩ := hT.exists_infDist_eq_dist hTne p
  have h1 : dist p q ≤ hausdorffDist S T := by
    rw [← hpq]
    exact infDist_le_hausdorffDist_of_mem hp (hausdorffEDist_ne_top_of_isCompact hS hT hSne hTne)
  have h2 : ⟪p, u t⟫ = ⟪q, u t⟫ + ⟪p - q, u t⟫ := by rw [inner_sub_left]; ring
  have h3 : ⟪p - q, u t⟫ ≤ dist p q := by
    rw [dist_eq_norm]
    calc ⟪p - q, u t⟫ ≤ ‖p - q‖ * ‖u t‖ := real_inner_le_norm _ _
      _ = ‖p - q‖ := by rw [norm_u, mul_one]
  linarith [le_supportFn hT hq t]

/-- Half of Schneider's Lemma 1.8.14: `|h_S(t) - h_T(t)| ≤ d_H(S, T)`. -/
theorem abs_supportFn_sub_le_hausdorffDist {S T : Set ℝ²} (hS : IsCompact S) (hT : IsCompact T)
    (hSne : S.Nonempty) (hTne : T.Nonempty) (t : ℝ) :
    |supportFn S t - supportFn T t| ≤ hausdorffDist S T := by
  have h1 := supportFn_le_add_hausdorffDist hS hT hSne hTne t
  have h2 := supportFn_le_add_hausdorffDist hT hS hTne hSne t
  rw [hausdorffDist_comm] at h2
  rw [abs_le]
  constructor <;> linarith

/-- Hausdorff convergence implies uniform convergence of support functions. -/
theorem tendsto_supportFn_uniformly {ι : Type*} {l : Filter ι} {K : ι → Set ℝ²} {L : Set ℝ²}
    (hK : ∀ i, IsCompact (K i)) (hKne : ∀ i, (K i).Nonempty) (hL : IsCompact L)
    (hLne : L.Nonempty) (hlim : Tendsto (fun i => hausdorffDist (K i) L) l (𝓝 0)) :
    TendstoUniformly (fun i => supportFn (K i)) (supportFn L) l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [(tendsto_order.1 hlim).2 ε hε] with i hi t
  rw [Real.dist_eq, abs_sub_comm]
  exact (abs_supportFn_sub_le_hausdorffDist (hK i) hL (hKne i) hLne t).trans_lt hi

/-! ## Lemma 3.5.3 -/

/-- **Lemma 3.5.3.** If `X_i ⊆ Y_i`, `X_i → X`, `Y_i → Y` in the Hausdorff distance (all sets
bounded and nonempty) and `Y` is closed, then `X ⊆ Y`. -/
theorem subset_of_tendsto_hausdorffDist {ι : Type*} {l : Filter ι} [l.NeBot]
    {X Y : ι → Set ℝ²} {X' Y' : Set ℝ²}
    (hXb : ∀ i, Bornology.IsBounded (X i)) (hXne : ∀ i, (X i).Nonempty)
    (hYb : ∀ i, Bornology.IsBounded (Y i)) (hYne : ∀ i, (Y i).Nonempty)
    (hX'b : Bornology.IsBounded X') (hY'b : Bornology.IsBounded Y') (hY'ne : Y'.Nonempty)
    (hY'c : IsClosed Y') (hsub : ∀ i, X i ⊆ Y i)
    (hX : Tendsto (fun i => hausdorffDist (X i) X') l (𝓝 0))
    (hY : Tendsto (fun i => hausdorffDist (Y i) Y') l (𝓝 0)) : X' ⊆ Y' := by
  intro p hp
  have hX'ne : X'.Nonempty := ⟨p, hp⟩
  rw [hY'c.mem_iff_infDist_zero hY'ne]
  refine le_antisymm ?_ infDist_nonneg
  have hbound : ∀ i, infDist p Y' ≤ hausdorffDist (X i) X' + hausdorffDist (Y i) Y' := by
    intro i
    have h1 := infDist_le_infDist_add_hausdorffDist (x := p)
      (hausdorffEDist_ne_top_of_nonempty_of_bounded (hYne i) hY'ne (hYb i) hY'b)
    have h2 : infDist p (Y i) ≤ infDist p (X i) := infDist_le_infDist_of_subset (hsub i) (hXne i)
    have h3 : infDist p (X i) ≤ hausdorffDist X' (X i) :=
      infDist_le_hausdorffDist_of_mem hp
        (hausdorffEDist_ne_top_of_nonempty_of_bounded hX'ne (hXne i) hX'b (hXb i))
    rw [hausdorffDist_comm] at h3
    linarith
  have hlim := hX.add hY
  rw [add_zero] at hlim
  exact ge_of_tendsto hlim (Eventually.of_forall hbound)

/-! ## Limits of convex sets; Blaschke selection -/

theorem convex_of_tendsto_hausdorffDist {ι : Type*} {l : Filter ι} [l.NeBot]
    {K : ι → Set ℝ²} {L : Set ℝ²} (hc : ∀ i, Convex ℝ (K i))
    (hb : ∀ i, Bornology.IsBounded (K i)) (hne : ∀ i, (K i).Nonempty)
    (hLc : IsClosed L) (hLb : Bornology.IsBounded L)
    (hlim : Tendsto (fun i => hausdorffDist (K i) L) l (𝓝 0)) : Convex ℝ L := by
  intro x hx y hy a b ha hb' hab
  have hLne : L.Nonempty := ⟨x, hx⟩
  rw [hLc.mem_iff_infDist_zero hLne]
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) infDist_nonneg
  obtain ⟨i, hi⟩ := ((tendsto_order.1 hlim).2 (ε / 2) (by positivity)).exists
  obtain ⟨x', hx', hxx'⟩ := exists_dist_lt_of_hausdorffDist_lt' hx hi
    (hausdorffEDist_ne_top_of_nonempty_of_bounded (hne i) hLne (hb i) hLb)
  obtain ⟨y', hy', hyy'⟩ := exists_dist_lt_of_hausdorffDist_lt' hy hi
    (hausdorffEDist_ne_top_of_nonempty_of_bounded (hne i) hLne (hb i) hLb)
  have hz' : a • x' + b • y' ∈ K i := hc i hx' hy' ha hb' hab
  have h1 : infDist (a • x' + b • y') L ≤ hausdorffDist (K i) L :=
    infDist_le_hausdorffDist_of_mem hz'
      (hausdorffEDist_ne_top_of_nonempty_of_bounded (hne i) hLne (hb i) hLb)
  have h2 : dist (a • x + b • y) (a • x' + b • y') ≤ ε / 2 := by
    rw [dist_eq_norm, show a • x + b • y - (a • x' + b • y') = a • (x - x') + b • (y - y') by
      module]
    calc ‖a • (x - x') + b • (y - y')‖ ≤ ‖a • (x - x')‖ + ‖b • (y - y')‖ := norm_add_le _ _
      _ = a * dist x x' + b * dist y y' := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb', dist_eq_norm,
          dist_eq_norm]
      _ ≤ a * (ε / 2) + b * (ε / 2) := by
        gcongr
        · rw [dist_comm]; exact hxx'.le
        · rw [dist_comm]; exact hyy'.le
      _ = ε / 2 := by rw [← add_mul, hab, one_mul]
  have h3 := infDist_le_infDist_add_dist (x := a • x + b • y) (y := a • x' + b • y') (s := L)
  linarith

/-- **Blaschke selection theorem** (plane): a sequence of convex bodies in a fixed ball has a
Hausdorff-convergent subsequence, whose limit is a convex body in the same ball. -/
theorem exists_tendsto_hausdorffDist {K : ℕ → Set ℝ²} {R : ℝ} (hK : ∀ n, IsCompact (K n))
    (hne : ∀ n, (K n).Nonempty) (hc : ∀ n, Convex ℝ (K n))
    (hR : ∀ n, K n ⊆ closedBall (0 : ℝ²) R) :
    ∃ (L : Set ℝ²) (φ : ℕ → ℕ), StrictMono φ ∧ IsCompact L ∧ L.Nonempty ∧ Convex ℝ L ∧
      L ⊆ closedBall (0 : ℝ²) R ∧
      Tendsto (fun n => hausdorffDist (K (φ n)) L) atTop (𝓝 0) := by
  let X : ℕ → TopologicalSpace.NonemptyCompacts ℝ² := fun n => ⟨⟨K n, hK n⟩, hne n⟩
  have hA := TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact
    (isCompact_closedBall (0 : ℝ²) R)
  obtain ⟨L, hLA, φ, hφ, hlim⟩ := hA.tendsto_subseq (x := X) (fun n => hR n)
  have hlim' : Tendsto (fun n => hausdorffDist (K (φ n)) (L : Set ℝ²)) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.1 hlim
  refine ⟨L, φ, hφ, L.isCompact, L.nonempty, ?_, hLA, hlim'⟩
  exact convex_of_tendsto_hausdorffDist (fun n => hc (φ n)) (fun n => (hK (φ n)).isBounded)
    (fun n => hne (φ n)) L.isCompact.isClosed L.isCompact.isBounded hlim'

/-! ## Nearest points and inner parallel bodies -/

/-- The variational inequality for a nearest point `q ∈ T` to `p` (T convex). -/
lemma inner_sub_nonpos_of_nearest {T : Set ℝ²} (hT : Convex ℝ T) {p q : ℝ²} (hq : q ∈ T)
    (hmin : ∀ y ∈ T, dist p q ≤ dist p y) {y : ℝ²} (hy : y ∈ T) : ⟪p - q, y - q⟫ ≤ 0 := by
  by_contra hpos
  push Not at hpos
  obtain ⟨N, hN⟩ : ∃ N, N = ‖y - q‖ ^ 2 := ⟨_, rfl⟩
  have key : ∀ r : ℝ, 0 ≤ r → r ≤ 1 → 2 * r * ⟪p - q, y - q⟫ ≤ r ^ 2 * N := by
    intro r hr0 hr1
    have hz : q + r • (y - q) ∈ T := by
      have := hT hq hy (by linarith : 0 ≤ 1 - r) hr0 (by ring)
      convert this using 1
      module
    have h := hmin _ hz
    rw [dist_eq_norm, dist_eq_norm] at h
    have h2 : ‖p - q‖ ^ 2 ≤ ‖p - (q + r • (y - q))‖ ^ 2 := by gcongr
    have e : ‖(p - q) - r • (y - q)‖ ^ 2 =
        ‖p - q‖ ^ 2 - 2 * (r * ⟪p - q, y - q⟫) + (r * ‖y - q‖) ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, Real.norm_of_nonneg hr0]
    rw [show p - (q + r • (y - q)) = (p - q) - r • (y - q) by abel, e] at h2
    rw [hN]
    nlinarith
  rcases le_or_gt N ⟪p - q, y - q⟫ with h | h
  · have := key 1 zero_le_one le_rfl
    linarith
  · have hN0 : 0 < N := lt_trans hpos h
    have := key (⟪p - q, y - q⟫ / N) (div_nonneg hpos.le hN0.le)
      ((div_le_one hN0).2 h.le)
    have e : (⟪p - q, y - q⟫ / N) ^ 2 * N = ⟪p - q, y - q⟫ / N * ⟪p - q, y - q⟫ := by
      field_simp
    rw [e] at this
    have hr : 0 < ⟪p - q, y - q⟫ / N := div_pos hpos hN0
    nlinarith [mul_pos hr hpos]

/-- If the closed `δ`-ball around `x` lies in `K` and the convex compact `T` is `δ`-close to `K`
(strictly) in the Hausdorff distance, then `x ∈ T`. -/
theorem mem_of_closedBall_subset {K T : Set ℝ²} (hT : IsCompact T) (hTne : T.Nonempty)
    (hTc : Convex ℝ T) (hKb : Bornology.IsBounded K) {x : ℝ²} {δ : ℝ}
    (hball : closedBall x δ ⊆ K) (hd : hausdorffDist K T < δ) : x ∈ T := by
  by_contra hx
  have hδ : 0 ≤ δ := hausdorffDist_nonneg.trans hd.le
  have hKne : K.Nonempty := ⟨x, hball (mem_closedBall_self hδ)⟩
  have hfin := hausdorffEDist_ne_top_of_nonempty_of_bounded hKne hTne hKb hT.isBounded
  obtain ⟨q, hq, hxq⟩ := hT.exists_infDist_eq_dist hTne x
  have hmin : ∀ y ∈ T, dist x q ≤ dist x y := fun y hy => hxq ▸ infDist_le_dist_of_mem hy
  have hne : x ≠ q := fun h => hx (h ▸ hq)
  have hpos : 0 < ‖x - q‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨w, hw⟩ : ∃ w : ℝ², w = ‖x - q‖⁻¹ • (x - q) := ⟨_, rfl⟩
  have hwn : ‖w‖ = 1 := by
    rw [hw, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le), inv_mul_cancel₀ hpos.ne']
  have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hwn, one_pow]
  have hz : x + δ • w ∈ K := hball (by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hwn, mul_one,
      Real.norm_of_nonneg hδ])
  have h1 : infDist (x + δ • w) T < δ := (infDist_le_hausdorffDist_of_mem hz hfin).trans_lt hd
  have h2 : δ + ‖x - q‖ ≤ infDist (x + δ • w) T := by
    rw [le_infDist hTne]
    intro y hy
    have hvi := inner_sub_nonpos_of_nearest hTc hq hmin hy
    have e1 : ⟪x - q, w⟫ = ‖x - q‖ := by
      rw [hw, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have e2 : ⟪y - q, w⟫ ≤ 0 := by
      rw [hw, real_inner_smul_right, real_inner_comm]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hpos.le) hvi
    have e3 : ⟪x + δ • w - y, w⟫ ≤ dist (x + δ • w) y := by
      rw [dist_eq_norm]
      calc ⟪x + δ • w - y, w⟫ ≤ ‖x + δ • w - y‖ * ‖w‖ := real_inner_le_norm _ _
        _ = ‖x + δ • w - y‖ := by rw [hwn, mul_one]
    have e4 : ⟪x + δ • w - y, w⟫ = ⟪x - q, w⟫ + δ * ⟪w, w⟫ - ⟪y - q, w⟫ := by
      rw [show x + δ • w - y = (x - q) + δ • w - (y - q) by abel, inner_sub_left, inner_add_left,
        real_inner_smul_left]
    rw [e4, e1, hww] at e3
    linarith
  linarith

end Sofa
