/-
# Sofa/TangentCap.lean — areas of tangent caps without Green's theorem (toward Baek §8.2)

* `volumeReal_eq_integral_sq_sub_sq_of_convex`: `|K| = ½∫_{t₀}^{t₀+2π}(h_K² − (e⁺_K)²)` for **every**
  nonempty compact convex `K` — round 28 needed a nonempty interior; we remove it by thickening
  `K` to `K + B̄(0, ε)` (support function `h_K + ε`, same `e⁺_K`) and letting `ε → 0`.
* `supportFn_convexHull_insert`: `h_{conv(K ∪ {W})} = max(⟪W, u_t⟫, h_K)`.
* For `a < b < a + π` and `W = v_K(a, b)` (the intersection of `l_K(a)` and `l_K(b)`):
  `⟪W, u_t⟫ ≥ h_K(t)` on `[a, b]` and `⟪W, u_t⟫ ≤ h_K(t)` on `[b, a + 2π]`.
* **The tangent-cap formula** (`volumeReal_convexHull_insert_vtx2`):

      |conv(K ∪ {v_K(a, b)})| = |K| + J(v⁺_K(a), v_K(a,b)) + J(v_K(a,b), v⁻_K(b)) − J(u^{a,b}_K).

  The region `conv(K ∪ {W}) \ K` is the region enclosed by the Jordan curve `Γ` in Baek's proof of
  Lemma 8.2.2 (the convex arc `u^{a,b}_K` closed by its two tangent segments); this formula is the
  only thing that proof takes from Green's theorem (Thm 7.2.3) and Lemma 7.3.5.

Proof of the formula: `h_C = ⟪W, u_t⟫` on `[a, b]` and `h_C = h_K` on `[b, a + 2π]`, so the classical
formula for `C = conv(K ∪ {W})` and for `K` differ only on `[a, b]`, where
`∫(⟪W,u⟫² − ⟪W,v⟫²) = [⟪W,u⟫⟪W,v⟫]` explicitly, and the closed form of `J(u^{a,b}_K)` (round 28).

STATUS: [PROOF-C-local] round 1 (2026-09-22, Opus 5.5).
-/
import Mathlib.Analysis.Convex.Join
import Sofa.ConcaveQ

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped Pointwise EuclideanGeometry RealInnerProductSpace Interval

namespace Sofa

variable {K : Set ℝ²}

/-! ## Thickening -/

/-- `K + B̄(0, ε)`. -/
def thick (K : Set ℝ²) (ε : ℝ) : Set ℝ² := K + Metric.closedBall (0 : ℝ²) ε

lemma supportFn_closedBall {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    supportFn (Metric.closedBall (0 : ℝ²) ε) t = ε := by
  have hB := isCompact_closedBall (0 : ℝ²) ε
  have hBne : (Metric.closedBall (0 : ℝ²) ε).Nonempty := ⟨0, Metric.mem_closedBall_self hε⟩
  apply le_antisymm
  · rw [supportFn_le_iff hB hBne]
    intro p hp
    calc ⟪p, u t⟫ ≤ ‖p‖ * ‖u t‖ := real_inner_le_norm _ _
      _ = ‖p‖ := by rw [norm_u, mul_one]
      _ ≤ ε := mem_closedBall_zero_iff.1 hp
  · have hm : ε • u t ∈ Metric.closedBall (0 : ℝ²) ε := by
      rw [mem_closedBall_zero_iff, norm_smul, norm_u, mul_one, Real.norm_of_nonneg hε]
    have := le_supportFn hB hm t
    rwa [real_inner_smul_left, inner_u_u, mul_one] at this

lemma isCompact_thick (hK : IsCompact K) (ε : ℝ) : IsCompact (thick K ε) :=
  hK.add (isCompact_closedBall _ _)

lemma convex_thick (hc : Convex ℝ K) (ε : ℝ) : Convex ℝ (thick K ε) :=
  hc.add (convex_closedBall _ _)

lemma nonempty_thick (hne : K.Nonempty) {ε : ℝ} (hε : 0 ≤ ε) : (thick K ε).Nonempty :=
  hne.add ⟨0, Metric.mem_closedBall_self hε⟩

lemma interior_thick_nonempty (hne : K.Nonempty) {ε : ℝ} (hε : 0 < ε) :
    (interior (thick K ε)).Nonempty := by
  obtain ⟨k, hk⟩ := hne
  refine ⟨k, mem_interior.2 ⟨Metric.ball k ε, ?_, Metric.isOpen_ball, Metric.mem_ball_self hε⟩⟩
  intro p hp
  rw [Metric.mem_ball, dist_eq_norm] at hp
  have hpk : k + (p - k) = p := by abel
  exact Set.mem_add.2 ⟨k, hk, p - k, mem_closedBall_zero_iff.2 hp.le, hpk⟩

lemma supportFn_thick (hK : IsCompact K) (hne : K.Nonempty) {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    supportFn (thick K ε) t = supportFn K t + ε := by
  rw [thick, supportFn_add hK (isCompact_closedBall _ _) hne ⟨0, Metric.mem_closedBall_self hε⟩,
    supportFn_closedBall hε]

/-- Two bodies whose support functions differ by a constant have the same `e⁺` (it is the right
derivative of the support function). -/
lemma edgeMax_eq_of_supportFn_eq_add {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty)
    (hB : IsCompact B) (hBne : B.Nonempty) {c : ℝ} (h : ∀ t, supportFn A t = supportFn B t + c)
    (t : ℝ) : edgeMax A t = edgeMax B t := by
  have hA' := hasDerivWithinAt_supportFn_Ioi hA hAne t
  have hB' := (hasDerivWithinAt_supportFn_Ioi hB hBne t).add_const c
  have e : (fun s => supportFn B s + c) = supportFn A := funext fun s => (h s).symm
  rw [e] at hB'
  exact (uniqueDiffWithinAt_Ioi t).eq_deriv _ hA' hB'

/-- **`|K| = ½∫(h_K² − h_K'²)` for every nonempty compact convex `K`** (no interior needed). -/
theorem volumeReal_eq_integral_sq_sub_sq_of_convex (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (t₀ : ℝ) :
    volume.real K = (∫ t in t₀..t₀ + 2 * π, (supportFn K t ^ 2 - edgeMax K t ^ 2)) / 2 := by
  have hc := continuous_supportFn hK hne
  have hi1 : IntervalIntegrable (fun t => supportFn K t ^ 2 - edgeMax K t ^ 2) volume t₀
      (t₀ + 2 * π) :=
    ((hc.pow 2).intervalIntegrable _ _).sub (intervalIntegrable_edgeMax_sq hK hne _ _)
  have hform : ∀ ε : ℝ, 0 < ε → volume.real (thick K ε)
      = (∫ t in t₀..t₀ + 2 * π, (supportFn K t ^ 2 - edgeMax K t ^ 2)) / 2
        + ε * (∫ t in t₀..t₀ + 2 * π, supportFn K t) + π * ε ^ 2 := by
    intro ε hε
    rw [volumeReal_eq_integral_sq_sub_sq (isCompact_thick hK ε) (convex_thick hconv ε)
      (interior_thick_nonempty hne hε) t₀]
    have hs := supportFn_thick hK hne hε.le
    have he := edgeMax_eq_of_supportFn_eq_add (isCompact_thick hK ε) (nonempty_thick hne hε.le)
      hK hne hs
    have e : ∀ t, supportFn (thick K ε) t ^ 2 - edgeMax (thick K ε) t ^ 2
        = (supportFn K t ^ 2 - edgeMax K t ^ 2) + (2 * ε * supportFn K t + ε ^ 2) := fun t => by
      rw [hs, he]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_add hi1 (((hc.intervalIntegrable _ _).const_mul _).add
      intervalIntegrable_const), intervalIntegral.integral_add
      ((hc.intervalIntegrable _ _).const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hlim1 : Tendsto (fun ε => volume.real (Metric.cthickening ε K)) (𝓝[>] 0)
      (𝓝 (volume.real K)) := by
    have h := tendsto_measure_cthickening_of_isCompact (μ := volume) hK
    exact ((ENNReal.tendsto_toReal hK.measure_lt_top.ne).comp h).mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto (fun ε => volume.real (Metric.cthickening ε K)) (𝓝[>] 0)
      (𝓝 ((∫ t in t₀..t₀ + 2 * π, (supportFn K t ^ 2 - edgeMax K t ^ 2)) / 2)) := by
    have hcont : Continuous fun ε : ℝ =>
        (∫ t in t₀..t₀ + 2 * π, (supportFn K t ^ 2 - edgeMax K t ^ 2)) / 2
          + ε * (∫ t in t₀..t₀ + 2 * π, supportFn K t) + π * ε ^ 2 := by fun_prop
    have h0 := hcont.tendsto' 0 ((∫ t in t₀..t₀ + 2 * π, (supportFn K t ^ 2 - edgeMax K t ^ 2)) / 2)
      (by simp)
    refine (h0.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← hK.add_closedBall_zero (le_of_lt hε)]
    exact (hform ε hε).symm
  exact tendsto_nhds_unique hlim1 hlim2

/-! ## The convex hull of `K ∪ {W}` -/

lemma convexHull_insert_eq_image (hconv : Convex ℝ K) (hne : K.Nonempty) (W : ℝ²) :
    convexHull ℝ (insert W K)
      = (fun q : ℝ × ℝ² => (1 - q.1) • W + q.1 • q.2) '' (Icc (0 : ℝ) 1 ×ˢ K) := by
  rw [convexHull_insert hne, hconv.convexHull_eq, convexJoin_singleton_left]
  ext p
  simp only [mem_iUnion, segment_eq_image, mem_image, mem_prod, Prod.exists, exists_prop]
  constructor
  · rintro ⟨b, hb, θ, hθ, rfl⟩
    exact ⟨θ, b, ⟨hθ, hb⟩, rfl⟩
  · rintro ⟨θ, b, ⟨hθ, hb⟩, rfl⟩
    exact ⟨b, hb, θ, hθ, rfl⟩

lemma isCompact_convexHull_insert (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (W : ℝ²) : IsCompact (convexHull ℝ (insert W K)) := by
  rw [convexHull_insert_eq_image hconv hne W]
  exact (isCompact_Icc.prod hK).image (by fun_prop)

/-- `h_{conv(K ∪ {W})} = max(⟪W, u_t⟫, h_K)`. -/
theorem supportFn_convexHull_insert (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (W : ℝ²) (t : ℝ) :
    supportFn (convexHull ℝ (insert W K)) t = max ⟪W, u t⟫ (supportFn K t) := by
  have hC := isCompact_convexHull_insert hK hconv hne W
  have hCne : (convexHull ℝ (insert W K)).Nonempty :=
    ⟨W, subset_convexHull ℝ _ (mem_insert W K)⟩
  apply le_antisymm
  · rw [supportFn_le_iff hC hCne]
    intro p hp
    have hsub : insert W K ⊆ hpLe t (max ⟪W, u t⟫ (supportFn K t)) := by
      rintro q (rfl | hq)
      · show ⟪q, u t⟫ ≤ max ⟪q, u t⟫ (supportFn K t)
        exact le_max_left _ _
      · show ⟪q, u t⟫ ≤ max ⟪W, u t⟫ (supportFn K t)
        exact (le_supportFn hK hq t).trans (le_max_right _ _)
    exact convexHull_min hsub (convex_hpLe _ _) hp
  · apply max_le
    · exact le_supportFn hC (subset_convexHull ℝ _ (mem_insert W K)) t
    · exact supportFn_mono hC hne ((subset_insert W K).trans (subset_convexHull ℝ _)) t

/-! ## `v_K(a, b)` against the support function -/

lemma sin_sub_smul_u (a b t : ℝ) :
    sin (b - a) • u t = sin (b - t) • u a + sin (t - a) • u b := by
  ext i; fin_cases i <;> simp [u, sin_sub] <;> ring

/-- On `[a, b]`, the corner `v_K(a, b)` is outside every supporting half-plane. -/
theorem supportFn_le_inner_vtx2 (hK : IsCompact K) (hne : K.Nonempty) {a b t : ℝ} (hab : a < b)
    (hba : b < a + π) (hta : a ≤ t) (htb : t ≤ b) :
    supportFn K t ≤ ⟪vtx2 K a b, u t⟫ := by
  have hs : 0 < sin (b - a) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hα : 0 ≤ sin (b - t) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hβ : 0 ≤ sin (t - a) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hW : ∀ p : ℝ², sin (b - a) * ⟪p, u t⟫
      = sin (b - t) * ⟪p, u a⟫ + sin (t - a) * ⟪p, u b⟫ := fun p => by
    rw [← real_inner_smul_right, sin_sub_smul_u, inner_add_right, real_inner_smul_right,
      real_inner_smul_right]
  have e1 := inner_vtx2_u_left K a b
  have e2 := inner_vtx2_u_right K (a := a) (b := b) hs.ne'
  rw [supportFn_le_iff hK hne]
  intro p hp
  have h1 := mul_le_mul_of_nonneg_left (le_supportFn hK hp a) hα
  have h2 := mul_le_mul_of_nonneg_left (le_supportFn hK hp b) hβ
  have h3 := hW p
  have h4 := hW (vtx2 K a b)
  rw [e1, e2] at h4
  refine le_of_mul_le_mul_left ?_ hs
  linarith

/-- Outside `[a, b]` (mod `2π`), `v_K(a, b)` is inside every supporting half-plane. -/
theorem inner_vtx2_le_supportFn (hK : IsCompact K) (hne : K.Nonempty) {a b t : ℝ} (hab : a < b)
    (hba : b < a + π) (htb : b ≤ t) (hta : t ≤ a + 2 * π) :
    ⟪vtx2 K a b, u t⟫ ≤ supportFn K t := by
  have hs : 0 < sin (b - a) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  set W := vtx2 K a b with hWdef
  obtain ⟨X, hX, hXa⟩ := exists_supportFn_eq hK hne a
  obtain ⟨Y, hY, hYb⟩ := exists_supportFn_eq hK hne b
  have hWa : ⟪W, u a⟫ = supportFn K a := inner_vtx2_u_left K a b
  have hWb : ⟪W, u b⟫ = supportFn K b := inner_vtx2_u_right K hs.ne'
  -- `W − X = λ v_a` with `λ ≥ 0`
  have hWX : W - X = ⟪W - X, v a⟫ • v a := by
    have h := decomp_u_v a (W - X)
    rwa [inner_sub_left, hWa, hXa, sub_self, zero_smul, zero_add] at h
  have hXt : ∀ s, ⟪W - X, u s⟫ = ⟪W - X, v a⟫ * sin (s - a) := fun s => by
    conv_lhs => rw [hWX]
    rw [real_inner_smul_left, inner_v_u_eq_sin]
  have hl : 0 ≤ ⟪W - X, v a⟫ := by
    have h' : 0 ≤ ⟪W - X, u b⟫ := by
      rw [inner_sub_left, hWb]; linarith [le_supportFn hK hX b]
    rw [hXt b] at h'
    by_contra hneg
    rw [not_le] at hneg
    linarith [mul_neg_of_neg_of_pos hneg hs]
  -- `W − Y = μ v_b` with `μ ≤ 0`
  have hWY : W - Y = ⟪W - Y, v b⟫ • v b := by
    have h := decomp_u_v b (W - Y)
    rwa [inner_sub_left, hWb, hYb, sub_self, zero_smul, zero_add] at h
  have hYt : ∀ s, ⟪W - Y, u s⟫ = ⟪W - Y, v b⟫ * sin (s - b) := fun s => by
    conv_lhs => rw [hWY]
    rw [real_inner_smul_left, inner_v_u_eq_sin]
  have hm : ⟪W - Y, v b⟫ ≤ 0 := by
    have h' : 0 ≤ ⟪W - Y, u a⟫ := by
      rw [inner_sub_left, hWa]; linarith [le_supportFn hK hY a]
    have hsab : sin (a - b) = -sin (b - a) := by rw [← sin_neg, neg_sub]
    rw [hYt a, hsab] at h'
    by_contra hpos
    rw [not_le] at hpos
    linarith [mul_pos hpos hs]
  by_cases ht : t ≤ b + π
  · -- `⟪W, u_t⟫ = ⟪Y, u_t⟫ + μ sin(t − b) ≤ ⟪Y, u_t⟫`
    have h := hYt t
    rw [inner_sub_left] at h
    have hsin : 0 ≤ sin (t - b) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    linarith [le_supportFn hK hY t, mul_nonpos_of_nonpos_of_nonneg hm hsin]
  · -- `t − a ∈ [π, 2π]`: `⟪W, u_t⟫ = ⟪X, u_t⟫ + λ sin(t − a) ≤ ⟪X, u_t⟫`
    rw [not_le] at ht
    have h := hXt t
    rw [inner_sub_left] at h
    have hsin : sin (t - a) ≤ 0 := by
      have := sin_nonpos_of_nonpos_of_neg_pi_le (x := t - a - 2 * π) (by linarith) (by linarith)
      rwa [sin_sub_two_pi] at this
    linarith [le_supportFn hK hX t, mul_nonpos_of_nonneg_of_nonpos hl hsin]

/-! ## The tangent-cap formula -/

lemma continuous_inner_u_arg (W : ℝ²) : Continuous fun s => ⟪W, u s⟫ :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_inner_u W t).continuousAt

lemma continuous_inner_v_arg (W : ℝ²) : Continuous fun s => ⟪W, v s⟫ := by
  have h : Continuous fun s => -⟪W, v s⟫ :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_inner_v W t).continuousAt
  have e : (fun s => ⟪W, v s⟫) = fun s => -(-⟪W, v s⟫) := by funext s; ring
  rw [e]
  exact h.neg

lemma integral_inner_u_sq_sub_inner_v_sq (W : ℝ²) (a b : ℝ) :
    ∫ t in a..b, (⟪W, u t⟫ ^ 2 - ⟪W, v t⟫ ^ 2)
      = ⟪W, u a⟫ * ⟪W, v a⟫ - ⟪W, u b⟫ * ⟪W, v b⟫ := by
  have hd : ∀ t, HasDerivAt (fun s => -(⟪W, u s⟫ * ⟪W, v s⟫)) (⟪W, u t⟫ ^ 2 - ⟪W, v t⟫ ^ 2) t := by
    intro t
    have h1 := hasDerivAt_inner_u W t
    have h2 : HasDerivAt (fun s => ⟪W, v s⟫) (-⟪W, u t⟫) t := by
      have e : (fun s => ⟪W, v s⟫) = fun s => -(-⟪W, v s⟫) := by funext s; ring
      rw [e]
      exact (hasDerivAt_inner_v W t).neg
    exact (h1.mul h2).neg.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)]
  · ring
  · exact ((((continuous_inner_u_arg W).pow 2).sub
      ((continuous_inner_v_arg W).pow 2)).intervalIntegrable _ _)

/-- **The tangent-cap formula**: for `a < b < a + π` and `W = v_K(a, b)`,
`|conv(K ∪ {W})| = |K| + J(v⁺_K(a), W) + J(W, v⁻_K(b)) − J(u^{a,b}_K)`. -/
theorem volumeReal_convexHull_insert_vtx2 (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) {a b : ℝ} (hab : a < b) (hba : b < a + π) :
    volume.real (convexHull ℝ (insert (vtx2 K a b) K))
      = volume.real K + segJ (vtxP K a) (vtx2 K a b) + segJ (vtx2 K a b) (vtxM K b)
        - convJ K a b := by
  have hpi := pi_pos
  set W := vtx2 K a b with hWdef
  set C := convexHull ℝ (insert W K) with hCdef
  have hC := isCompact_convexHull_insert hK hconv hne W
  have hCconv : Convex ℝ C := convex_convexHull ℝ _
  have hCne : C.Nonempty := ⟨W, subset_convexHull ℝ _ (mem_insert W K)⟩
  have hsC := supportFn_convexHull_insert hK hconv hne W
  have hin : ∀ t ∈ Icc a b, supportFn C t = ⟪W, u t⟫ := fun t ht => by
    rw [hsC, max_eq_left (supportFn_le_inner_vtx2 hK hne hab hba ht.1 ht.2)]
  have hout : ∀ t ∈ Icc b (a + 2 * π), supportFn C t = supportFn K t := fun t ht => by
    rw [hsC, max_eq_right (inner_vtx2_le_supportFn hK hne hab hba ht.1 ht.2)]
  -- `e⁺_C` a.e. on the two arcs
  have hdC := ae_deriv_supportFn hC hCne
  have hdK := ae_deriv_supportFn hK hne
  have e_in : ∀ᵐ t ∂volume, t ∈ Ι a b → edgeMax C t = ⟪W, v t⟫ := by
    filter_upwards [hdC, (countable_singleton b).ae_notMem volume] with t ht htb hmem
    rw [uIoc_of_le hab.le] at hmem
    have hmem' : t ∈ Ioo a b := ⟨hmem.1, lt_of_le_of_ne hmem.2 (by simpa using htb)⟩
    rw [← ht]
    have hev : supportFn C =ᶠ[𝓝 t] fun s => ⟪W, u s⟫ := by
      filter_upwards [Ioo_mem_nhds hmem'.1 hmem'.2] with s hs using hin s (Ioo_subset_Icc_self hs)
    rw [hev.deriv_eq]
    exact (hasDerivAt_inner_u W t).deriv
  have e_out : ∀ᵐ t ∂volume, t ∈ Ι b (a + 2 * π) → edgeMax C t = edgeMax K t := by
    filter_upwards [hdC, hdK, (countable_singleton (a + 2 * π)).ae_notMem volume]
      with t hCt hKt htb hmem
    rw [uIoc_of_le (by linarith)] at hmem
    have hmem' : t ∈ Ioo b (a + 2 * π) := ⟨hmem.1, lt_of_le_of_ne hmem.2 (by simpa using htb)⟩
    rw [← hCt, ← hKt]
    have hev : supportFn C =ᶠ[𝓝 t] supportFn K := by
      filter_upwards [Ioo_mem_nhds hmem'.1 hmem'.2] with s hs using hout s (Ioo_subset_Icc_self hs)
    exact hev.deriv_eq
  -- the two classical formulas
  have VC := volumeReal_eq_integral_sq_sub_sq_of_convex hC hCconv hCne a
  have VK := volumeReal_eq_integral_sq_sub_sq_of_convex hK hconv hne a
  have hiC : ∀ x y, IntervalIntegrable (fun t => supportFn C t ^ 2 - edgeMax C t ^ 2) volume x y :=
    fun x y => (((continuous_supportFn hC hCne).pow 2).intervalIntegrable x y).sub
      (intervalIntegrable_edgeMax_sq hC hCne x y)
  have hiK : ∀ x y, IntervalIntegrable (fun t => supportFn K t ^ 2 - edgeMax K t ^ 2) volume x y :=
    fun x y => (((continuous_supportFn hK hne).pow 2).intervalIntegrable x y).sub
      (intervalIntegrable_edgeMax_sq hK hne x y)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hiC a b) (hiC b (a + 2 * π))] at VC
  rw [← intervalIntegral.integral_add_adjacent_intervals (hiK a b) (hiK b (a + 2 * π))] at VK
  have I1 : ∫ t in a..b, (supportFn C t ^ 2 - edgeMax C t ^ 2)
      = ⟪W, u a⟫ * ⟪W, v a⟫ - ⟪W, u b⟫ * ⟪W, v b⟫ := by
    rw [← integral_inner_u_sq_sub_inner_v_sq]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [e_in] with t ht hmem
    have hmem' : t ∈ Icc a b := by
      rw [uIoc_of_le hab.le] at hmem
      exact Ioc_subset_Icc_self hmem
    rw [ht hmem, hin t hmem']
  have I2 : ∫ t in b..(a + 2 * π), (supportFn C t ^ 2 - edgeMax C t ^ 2)
      = ∫ t in b..(a + 2 * π), (supportFn K t ^ 2 - edgeMax K t ^ 2) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [e_out] with t ht hmem
    have hmem' : t ∈ Icc b (a + 2 * π) := by
      rw [uIoc_of_le (by linarith)] at hmem
      exact Ioc_subset_Icc_self hmem
    rw [ht hmem, hout t hmem']
  have hJ := two_mul_convJ_eq hK hne hab
  -- the two segments
  have hWa : ⟪W, u a⟫ = supportFn K a := inner_vtx2_u_left K a b
  have hWb : ⟪W, u b⟫ = supportFn K b :=
    inner_vtx2_u_right K (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  have s1 : segJ (vtxP K a) W = supportFn K a * (⟪W, v a⟫ - edgeMax K a) / 2 := by
    rw [segJ_on_line (inner_vtxP_u K a) hWa, inner_sub_left, inner_vtxP_v]
  have s2 : segJ W (vtxM K b) = supportFn K b * (edgeMin K b - ⟪W, v b⟫) / 2 := by
    rw [segJ_on_line hWb (inner_vtxM_u K b), inner_sub_left, inner_vtxM_v]
  rw [I1, I2, hWa, hWb] at VC
  rw [VC, VK, s1, s2]
  linear_combination (1 / 2 : ℝ) * hJ

end Sofa
