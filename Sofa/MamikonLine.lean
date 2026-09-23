/-
# Sofa/MamikonLine.lean — the Mamikon regions used in Chapter 8

Chapter 8 (Defs 8.3.2–8.3.3) uses two kinds of Mamikon regions.

**Along a fixed supporting line.**  Baek's Def 8.3.1 parametrises the supporting line `l_K(t)` by
the normal angle `s` of the *other* supporting line through the point:

    `l^t_K(s) = v_K(s, t)`  for `s < t`,    `l^t_K(t) = v⁻_K(t)`.

Since `v_K(s, t)` is on `l_K(s)` with `v_s`-coordinate
`lineW K t s = (h(t) − h(s) cos(t − s)) / sin(t − s)`, the curve `s ↦ v_K(s, t)` is the
`tanCurve K (lineW K t)` of `Sofa/Mamikon.lean` (`vtx2_eq_tanCurve`, definitionally), and since it
also moves along the fixed line `l_K(t)`, its curve area functional is that of the segment between
its endpoints (`curveJ_vtx2`, Baek Thm 8.3.1).  So the Mamikon area of Def 7.4.2 is

    `mamikonSeg K a b t = J(v⁺(a), l(a)) + J(l(a), l(b)) + J(l(b), v⁻(b)) − J(u^{a,b}_K)`,

and Mamikon's theorem gives `mamikonSeg K a b t = ½∫_a^b (lineW K t − e⁺_K)²` for `b < t`
(`mamikonSeg_eq`).  The endpoint case `b = t` (used by `ℛ_B`, `ℒ_D` and the fourth region of
`𝒮_K`) is reached by letting `b ↑ t` (`tendsto_mamikonSeg_left`); convexity in `K` survives the
limit (`mamikonSeg_mix_le_self`), which is all Chapter 8 needs of it.

**Along the outer corner.**  The second region of `𝒮_K` follows `y_K(t) = h(t)u_t + h(t+π/2)v_t`,
which is `tanCurve K (h(· + π/2))` (`outerCorner_eq_tanCurve`).

**The inner corner.**  `𝒬` itself contains `J(x_K|[φ^R, φ^L])`.  For a curve `a(t)u_t + b(t)v_t`
with `a, b` absolutely continuous, `2J = ∫(a² + b² + a b' − b a')` (`two_mul_curveJ_frame`), and
`x_K = y_K − u_t − v_t`, so `J(y_K) − J(x_K) = ∫(h + g − 1) + ½[g − h]`, `g = h(· + π/2)`
(`curveJ_outer_sub_inner`), which is convex-linear in `K` (Baek Lemma 8.3.6 (1)).

STATUS: [PROOF-C-local] round 1 (2026-09-22, Opus 5.5).
-/
import Sofa.Mamikon

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace Interval

namespace Sofa

variable {K : Set ℝ²}

/-! ## Absolute continuity helpers -/

lemma ac_const (c : ℝ) (a b : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
  (contDiffOn_const (c := c)).absolutelyContinuousOnInterval

lemma ac_cos_sub (t : ℝ) (a b : ℝ) : AbsolutelyContinuousOnInterval (fun s => cos (t - s)) a b :=
  ((Real.contDiff_cos.comp (contDiff_const.sub contDiff_id)).contDiffOn
    (n := 1)).absolutelyContinuousOnInterval

lemma ac_sin_sub (t : ℝ) (a b : ℝ) : AbsolutelyContinuousOnInterval (fun s => sin (t - s)) a b :=
  ((Real.contDiff_sin.comp (contDiff_const.sub contDiff_id)).contDiffOn
    (n := 1)).absolutelyContinuousOnInterval

lemma ac_inv_sin_sub {t a b : ℝ} (h : ∀ s ∈ uIcc a b, sin (t - s) ≠ 0) :
    AbsolutelyContinuousOnInterval (fun s => (sin (t - s))⁻¹) a b :=
  (((Real.contDiff_sin.comp (contDiff_const.sub contDiff_id)).contDiffOn (n := 1)).inv
    h).absolutelyContinuousOnInterval

lemma ac_supportFn_add (hK : IsCompact K) (hne : K.Nonempty) (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun s => supportFn K (s + c)) a b := by
  obtain ⟨R, hR0, hR⟩ := exists_radius hK hne
  refine LipschitzOnWith.absolutelyContinuousOnInterval (K := Real.toNNReal R) ?_
  refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun s t => ?_)
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hR0]
  have := abs_supportFn_sub_le hK hne hR (s + c) (t + c)
  rwa [show s + c - (t + c) = s - t by ring] at this

/-! ## The line curve `l^t_K` (Def 8.3.1) -/

/-- The `v_s`-coordinate of `v_K(s, t)`. -/
def lineW (K : Set ℝ²) (t s : ℝ) : ℝ :=
  (supportFn K t - supportFn K s * cos (t - s)) / sin (t - s)

/-- `v_K(s, t)` lies on `l_K(s)`, with `v_s`-coordinate `lineW K t s`. -/
lemma vtx2_eq_tanCurve (K : Set ℝ²) (s t : ℝ) : vtx2 K s t = tanCurve K (lineW K t) s := rfl

/-- **Baek Def 8.3.1**: `l^t_K(s) = v_K(s, t)` for `s < t` and `l^t_K(t) = v⁻_K(t)`. -/
def lineCurve (K : Set ℝ²) (t s : ℝ) : ℝ² := if s < t then vtx2 K s t else vtxM K t

lemma lineCurve_of_lt {t s : ℝ} (h : s < t) : lineCurve K t s = vtx2 K s t := if_pos h

lemma lineCurve_self (t : ℝ) : lineCurve K t t = vtxM K t := if_neg (lt_irrefl t)

/-- On `[a, b]` with `b < t < a + π`, `sin (t − s) > 0`. -/
lemma sin_sub_pos_of_mem {a b t s : ℝ} (hab : a ≤ b) (hbt : b < t) (hta : t - a < π)
    (hs : s ∈ uIcc a b) : 0 < sin (t - s) := by
  rw [uIcc_of_le hab] at hs
  exact sin_pos_of_pos_of_lt_pi (by linarith [hs.2]) (by linarith [hs.1])

/-- `lineW K t` is absolutely continuous on `[a, b]` when `b < t < a + π`. -/
theorem ac_lineW (hK : IsCompact K) (hne : K.Nonempty) {a b t : ℝ} (hab : a ≤ b) (hbt : b < t)
    (hta : t - a < π) : AbsolutelyContinuousOnInterval (lineW K t) a b := by
  have hsin : ∀ s ∈ uIcc a b, sin (t - s) ≠ 0 := fun s hs =>
    (sin_sub_pos_of_mem hab hbt hta hs).ne'
  have h1 : AbsolutelyContinuousOnInterval
      (fun s => supportFn K t - supportFn K s * cos (t - s)) a b :=
    (ac_const _ a b).fun_sub
      ((absolutelyContinuousOnInterval_supportFn hK hne a b).fun_mul (ac_cos_sub t a b))
  have h := h1.fun_mul (ac_inv_sin_sub hsin)
  have e : lineW K t = fun s => (supportFn K t - supportFn K s * cos (t - s)) * (sin (t - s))⁻¹ := by
    funext s; rw [lineW, div_eq_mul_inv]
  rw [e]; exact h

/-- `v_K(s, t)` is on the fixed line `l_K(t)`: `v_K(s,t) = h(t) u_t + ⟪v_K(s,t), v_t⟫ v_t`. -/
lemma vtx2_eq_line (K : Set ℝ²) {s t : ℝ} (h : sin (t - s) ≠ 0) :
    vtx2 K s t = supportFn K t • u t + ⟪vtx2 K s t, v t⟫ • v t := by
  conv_lhs => rw [decomp_u_v t (vtx2 K s t)]
  rw [inner_vtx2_u_right K h]

/-- The position of `v_K(s, t)` along `l_K(t)`: `h(s) sin(s − t) + lineW K t s · cos(t − s)`. -/
lemma inner_vtx2_v_right (K : Set ℝ²) (s t : ℝ) :
    ⟪vtx2 K s t, v t⟫ = supportFn K s * sin (s - t) + lineW K t s * cos (t - s) := by
  rw [vtx2_eq_tanCurve, tanCurve, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_u_v_eq_sin, inner_v_v_eq_cos]

theorem ac_vtx2_v_right (hK : IsCompact K) (hne : K.Nonempty) {a b t : ℝ} (hab : a ≤ b)
    (hbt : b < t) (hta : t - a < π) :
    AbsolutelyContinuousOnInterval (fun s => ⟪vtx2 K s t, v t⟫) a b := by
  have e : (fun s => ⟪vtx2 K s t, v t⟫)
      = fun s => supportFn K s * sin (s - t) + lineW K t s * cos (t - s) :=
    funext fun s => inner_vtx2_v_right K s t
  rw [e]
  have hsin' : AbsolutelyContinuousOnInterval (fun s => sin (s - t)) a b :=
    ((Real.contDiff_sin.comp (contDiff_id.sub contDiff_const)).contDiffOn
      (n := 1)).absolutelyContinuousOnInterval
  exact ((absolutelyContinuousOnInterval_supportFn hK hne a b).fun_mul hsin').fun_add
    ((ac_lineW hK hne hab hbt hta).fun_mul (ac_cos_sub t a b))

/-- **Baek Theorem 8.3.1**: `J(l^t_K|[a,b]) = J(l^t_K(a), l^t_K(b))` for `b < t < a + π`. -/
theorem curveJ_vtx2 (hK : IsCompact K) (hne : K.Nonempty) {a b t : ℝ} (hab : a ≤ b)
    (hbt : b < t) (hta : t - a < π) :
    curveJ (fun s => vtx2 K s t) a b = segJ (vtx2 K a t) (vtx2 K b t) := by
  have hsin : ∀ s ∈ Icc a b, sin (t - s) ≠ 0 := fun s hs =>
    (sin_sub_pos_of_mem hab hbt hta (by rw [uIcc_of_le hab]; exact hs)).ne'
  have hrep : EqOn (fun s => vtx2 K s t)
      (fun s => supportFn K t • u t + ⟪vtx2 K s t, v t⟫ • v t) (Icc a b) :=
    fun s hs => vtx2_eq_line K (hsin s hs)
  rw [curveJ_congr hab hrep, curveJ_line (ac_vtx2_v_right hK hne hab hbt hta),
    ← vtx2_eq_line K (hsin a ⟨le_rfl, hab⟩), ← vtx2_eq_line K (hsin b ⟨hab, le_rfl⟩)]

/-! ## The Mamikon region along `l^t_K` -/

/-- The Mamikon region of Def 7.4.2 for `z = l^t_K` on `[a, b]`, `b ≤ t`, with its curve part
evaluated by Thm 8.3.1. -/
def mamikonSeg (K : Set ℝ²) (a b t : ℝ) : ℝ :=
  segJ (vtxP K a) (lineCurve K t a) + segJ (lineCurve K t a) (lineCurve K t b)
    + segJ (lineCurve K t b) (vtxM K b) - convJ K a b

/-- **Mamikon's theorem along a supporting line** (`b < t < a + π`). -/
theorem mamikonSeg_eq (hK : IsCompact K) (hne : K.Nonempty) {a b t : ℝ} (hab : a < b)
    (hbt : b < t) (hta : t - a < π) :
    mamikonSeg K a b t = (∫ s in a..b, (lineW K t s - edgeMax K s) ^ 2) / 2 := by
  rw [← mamikonM_eq hK hne hab (ac_lineW hK hne hab.le hbt hta), mamikonM, mamikonSeg,
    lineCurve_of_lt (hab.trans hbt), lineCurve_of_lt hbt]
  have hJ := curveJ_vtx2 hK hne hab.le hbt hta
  have e : (fun s => vtx2 K s t) = tanCurve K (lineW K t) := rfl
  rw [e] at hJ
  rw [hJ]
  rfl

/-! ## Continuity of the boundary terms as `b ↑ t` -/

lemma continuous_segJ : Continuous (fun p : ℝ² × ℝ² => segJ p.1 p.2) := by
  simp only [segJ, cross]
  fun_prop

lemma tendsto_segJ {α : Type*} {l : Filter α} {f g : α → ℝ²} {p q : ℝ²}
    (hf : Tendsto f l (𝓝 p)) (hg : Tendsto g l (𝓝 q)) :
    Tendsto (fun x => segJ (f x) (g x)) l (𝓝 (segJ p q)) :=
  (continuous_segJ.tendsto (p, q)).comp (hf.prodMk_nhds hg)

lemma tendsto_lineCurve_left (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    Tendsto (lineCurve K t) (𝓝[<] t) (𝓝 (lineCurve K t t)) := by
  rw [lineCurve_self]
  refine (tendsto_vtx2_left hK hne t).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (lineCurve_of_lt hs).symm

lemma tendsto_edgeMin_left (hK : IsCompact K) (hne : K.Nonempty) (t : ℝ) :
    Tendsto (edgeMin K) (𝓝[<] t) (𝓝 (edgeMin K t)) := by
  have h := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_vtxM_left hK hne t)
    ((continuous_v.tendsto t).mono_left nhdsWithin_le_nhds)
  rw [inner_vtxM_v] at h
  refine h.congr fun s => ?_
  exact inner_vtxM_v K s

/-- `J(u^{a,b}_K)` is left-continuous in `b` (from the closed form `two_mul_convJ_eq`). -/
lemma tendsto_convJ_left (hK : IsCompact K) (hne : K.Nonempty) {a t : ℝ} (hat : a < t) :
    Tendsto (fun b => convJ K a b) (𝓝[<] t) (𝓝 (convJ K a t)) := by
  have hcf : ∀ b, a < b → convJ K a b
      = (supportFn K b * edgeMin K b - supportFn K a * edgeMax K a
        + ∫ s in a..b, (supportFn K s ^ 2 - edgeMax K s ^ 2)) / 2 := by
    intro b hb
    have := two_mul_convJ_eq hK hne hb
    linarith
  have hint : ∀ x y : ℝ,
      IntervalIntegrable (fun s => supportFn K s ^ 2 - edgeMax K s ^ 2) volume x y :=
    fun x y => (((continuous_supportFn hK hne).pow 2).intervalIntegrable x y).sub
      (intervalIntegrable_edgeMax_sq hK hne x y)
  have hprim : Continuous fun b => ∫ s in a..b, (supportFn K s ^ 2 - edgeMax K s ^ 2) :=
    intervalIntegral.continuous_primitive hint a
  have h1 : Tendsto (fun b => (supportFn K b * edgeMin K b - supportFn K a * edgeMax K a
      + ∫ s in a..b, (supportFn K s ^ 2 - edgeMax K s ^ 2)) / 2) (𝓝[<] t)
      (𝓝 ((supportFn K t * edgeMin K t - supportFn K a * edgeMax K a
        + ∫ s in a..t, (supportFn K s ^ 2 - edgeMax K s ^ 2)) / 2)) := by
    refine ((((continuous_supportFn hK hne).tendsto t).mono_left nhdsWithin_le_nhds).mul
      (tendsto_edgeMin_left hK hne t) |>.sub tendsto_const_nhds |>.add
      ((hprim.tendsto t).mono_left nhdsWithin_le_nhds)).div_const 2
  rw [hcf t hat]
  refine h1.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hat] with b hb
  exact (hcf b hb.1).symm

/-- `mamikonSeg K a b t` is left-continuous in `b` at `b = t`. -/
theorem tendsto_mamikonSeg_left (hK : IsCompact K) (hne : K.Nonempty) {a t : ℝ} (hat : a < t) :
    Tendsto (fun b => mamikonSeg K a b t) (𝓝[<] t) (𝓝 (mamikonSeg K a t t)) := by
  unfold mamikonSeg
  exact (((tendsto_const_nhds.add (tendsto_segJ tendsto_const_nhds
    (tendsto_lineCurve_left hK hne t))).add
    (tendsto_segJ (tendsto_lineCurve_left hK hne t) (tendsto_vtxM_left hK hne t))).sub
    (tendsto_convJ_left hK hne hat))

/-! ## Convexity in `K` (Thm 7.4.2 for these regions) -/

lemma lineW_mix {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (t s : ℝ) :
    lineW (mix l A B) t s = (1 - l) * lineW A t s + l * lineW B t s := by
  rw [lineW, lineW, lineW, supportFn_mix hA hAne hB hBne hl0 hl1,
    supportFn_mix hA hAne hB hBne hl0 hl1]
  rcases eq_or_ne (sin (t - s)) 0 with h | h
  · rw [h, div_zero, div_zero, div_zero]; ring
  · field_simp; ring

/-- The pointwise convexity of `x ↦ x²`, integrated. -/
lemma integral_sq_mix_le {a b l : ℝ} (hab : a ≤ b) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable (fun s => f s ^ 2) volume a b)
    (hg : IntervalIntegrable (fun s => g s ^ 2) volume a b)
    (hfg : IntervalIntegrable (fun s => ((1 - l) * f s + l * g s) ^ 2) volume a b) :
    ∫ s in a..b, ((1 - l) * f s + l * g s) ^ 2
      ≤ (1 - l) * (∫ s in a..b, f s ^ 2) + l * ∫ s in a..b, g s ^ 2 := by
  have hpt : ∀ s, ((1 - l) * f s + l * g s) ^ 2 ≤ (1 - l) * f s ^ 2 + l * g s ^ 2 := by
    intro s
    have h := mul_nonneg (mul_nonneg hl0 (sub_nonneg.2 hl1)) (sq_nonneg (f s - g s))
    nlinarith [h]
  have hmono := intervalIntegral.integral_mono_on hab hfg ((hf.const_mul (1 - l)).add
    (hg.const_mul l)) (fun s _ => hpt s)
  rwa [intervalIntegral.integral_add (hf.const_mul (1 - l)) (hg.const_mul l),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono

/-- For `f` absolutely continuous and `e⁺_K`, `(f − e⁺_K)²` is interval integrable. -/
lemma intervalIntegrable_sub_edgeMax_sq (hK : IsCompact K) (hne : K.Nonempty) {f : ℝ → ℝ}
    {a b : ℝ} (hf : ContinuousOn f (uIcc a b)) :
    IntervalIntegrable (fun s => (f s - edgeMax K s) ^ 2) volume a b := by
  have e : (fun s => (f s - edgeMax K s) ^ 2)
      = fun s => f s ^ 2 - 2 * (f s * edgeMax K s) + edgeMax K s ^ 2 := by funext s; ring
  rw [e]
  exact ((hf.pow 2).intervalIntegrable.sub
    (((intervalIntegrable_edgeMax hK hne a b).continuousOn_mul hf).const_mul 2)).add
    (intervalIntegrable_edgeMax_sq hK hne a b)

/-- **Thm 7.4.2 along a supporting line** (`b < t`): `K ↦ M_K(a, b; l^t_K)` is convex. -/
theorem mamikonSeg_mix_le {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty)
    (hB : IsCompact B) (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {a b t : ℝ}
    (hab : a < b) (hbt : b < t) (hta : t - a < π) :
    mamikonSeg (mix l A B) a b t ≤ (1 - l) * mamikonSeg A a b t + l * mamikonSeg B a b t := by
  have hM := isCompact_mix (l := l) hA hB
  have hMne := nonempty_mix (l := l) hAne hBne
  rw [mamikonSeg_eq hM hMne hab hbt hta, mamikonSeg_eq hA hAne hab hbt hta,
    mamikonSeg_eq hB hBne hab hbt hta]
  have e : ∀ s, lineW (mix l A B) t s - edgeMax (mix l A B) s
      = (1 - l) * (lineW A t s - edgeMax A s) + l * (lineW B t s - edgeMax B s) := by
    intro s
    rw [lineW_mix hA hAne hB hBne hl0 hl1, edgeMax_mix hA hAne hB hBne hl0 hl1]; ring
  simp only [e]
  have iA := intervalIntegrable_sub_edgeMax_sq hA hAne (ac_lineW hA hAne hab.le hbt hta).continuousOn
  have iB := intervalIntegrable_sub_edgeMax_sq hB hBne (ac_lineW hB hBne hab.le hbt hta).continuousOn
  have iM : IntervalIntegrable (fun s => ((1 - l) * (lineW A t s - edgeMax A s)
      + l * (lineW B t s - edgeMax B s)) ^ 2) volume a b := by
    have h := intervalIntegrable_sub_edgeMax_sq hM hMne
      (ac_lineW hM hMne hab.le hbt hta).continuousOn
    simp only [e] at h
    exact h
  have := integral_sq_mix_le hab.le hl0 hl1 iA iB iM
  linarith

/-- **Thm 7.4.2 up to the endpoint** (`b = t`): convexity survives the limit `b ↑ t`. -/
theorem mamikonSeg_mix_le_self {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty)
    (hB : IsCompact B) (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {a t : ℝ}
    (hat : a < t) (hta : t - a < π) :
    mamikonSeg (mix l A B) a t t ≤ (1 - l) * mamikonSeg A a t t + l * mamikonSeg B a t t := by
  have hM := isCompact_mix (l := l) hA hB
  have hMne := nonempty_mix (l := l) hAne hBne
  have h1 := tendsto_mamikonSeg_left hM hMne hat
  have h2 := ((tendsto_mamikonSeg_left hA hAne hat).const_mul (1 - l)).add
    ((tendsto_mamikonSeg_left hB hBne hat).const_mul l)
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [Ioo_mem_nhdsLT hat] with b hb
  exact mamikonSeg_mix_le hA hAne hB hBne hl0 hl1 hb.1 hb.2 (by linarith [hb.1])

/-! ## The region along the outer corner -/

lemma outerCorner_eq_tanCurve (K : Set ℝ²) :
    outerCorner K = tanCurve K (fun s => supportFn K (s + π / 2)) := rfl

/-- **Mamikon's theorem along `y_K`**. -/
theorem mamikonM_outerCorner (hK : IsCompact K) (hne : K.Nonempty) {a b : ℝ} (hab : a < b) :
    mamikonM K a b (outerCorner K)
      = (∫ s in a..b, (supportFn K (s + π / 2) - edgeMax K s) ^ 2) / 2 := by
  rw [outerCorner_eq_tanCurve]
  exact mamikonM_eq hK hne hab (ac_supportFn_add hK hne _ a b)

/-- **Thm 7.4.2 along `y_K`**: `K ↦ M_K(a, b; y_K)` is convex. -/
theorem mamikonM_outerCorner_mix_le {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty)
    (hB : IsCompact B) (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) {a b : ℝ}
    (hab : a < b) :
    mamikonM (mix l A B) a b (outerCorner (mix l A B))
      ≤ (1 - l) * mamikonM A a b (outerCorner A) + l * mamikonM B a b (outerCorner B) := by
  rw [outerCorner_eq_tanCurve, outerCorner_eq_tanCurve, outerCorner_eq_tanCurve]
  have e : (fun s => supportFn (mix l A B) (s + π / 2))
      = fun s => (1 - l) * supportFn A (s + π / 2) + l * supportFn B (s + π / 2) :=
    funext fun s => supportFn_mix hA hAne hB hBne hl0 hl1 _
  rw [e]
  exact mamikonM_mix_le hA hAne hB hBne hl0 hl1 hab (ac_supportFn_add hA hAne _ a b)
    (ac_supportFn_add hB hBne _ a b)

/-! ## Curves in the moving frame, and the inner corner -/

/-- `(a u + b v)' = (a' − b) u + (a + b') v`. -/
lemma hasDerivAt_frame {a b : ℝ → ℝ} {t a' b' : ℝ} (ha : HasDerivAt a a' t)
    (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => a s • u s + b s • v s) ((a' - b t) • u t + (a t + b') • v t) t := by
  have h3 := (ha.smul (hasDerivAt_u t)).add (hb.smul (hasDerivAt_v t))
  have e : a t • v t + a' • u t + (b t • -u t + b' • v t)
      = (a' - b t) • u t + (a t + b') • v t := by
    rw [smul_neg, sub_smul, add_smul]; abel
  rw [e] at h3
  exact h3

/-- **A curve in the moving frame**: for `z(t) = a(t) u_t + b(t) v_t` with `a, b` absolutely
continuous on `[p, q]`, `2 J(z) = ∫_p^q (a² + b² + a b' − b a')`. -/
theorem two_mul_curveJ_frame {a b : ℝ → ℝ} {p q : ℝ} (ha : AbsolutelyContinuousOnInterval a p q)
    (hb : AbsolutelyContinuousOnInterval b p q) :
    2 * curveJ (fun t => a t • u t + b t • v t) p q
      = ∫ t in p..q, (a t ^ 2 + b t ^ 2 + a t * deriv b t - b t * deriv a t) := by
  have hae : ∀ᵐ t ∂volume, t ∈ Ι p q →
      cross (a t • u t + b t • v t) (deriv (fun s => a s • u s + b s • v s) t)
        = a t ^ 2 + b t ^ 2 + a t * deriv b t - b t * deriv a t := by
    filter_upwards [ha.ae_differentiableAt, hb.ae_differentiableAt] with t hta htb ht
    have hd := hasDerivAt_frame (hta (uIoc_subset_uIcc ht)).hasDerivAt
      (htb (uIoc_subset_uIcc ht)).hasDerivAt
    rw [hd.deriv, cross_frame]; ring
  rw [curveJ, intervalIntegral.integral_congr_ae hae]; ring

/-- **Baek Lemma 8.3.6 (1)**, in closed form: `J(y_K) − J(x_K) = ∫(h + g − 1) + ½[g − h]`
with `g = h(· + π/2)`.  The right side is convex-linear in `K`. -/
theorem curveJ_outer_sub_inner (hK : IsCompact K) (hne : K.Nonempty) (p q : ℝ) :
    curveJ (outerCorner K) p q - curveJ (innerCorner K) p q
      = (∫ t in p..q, (supportFn K t + supportFn K (t + π / 2) - 1))
        + ((supportFn K (q + π / 2) - supportFn K q)
          - (supportFn K (p + π / 2) - supportFn K p)) / 2 := by
  have hh := absolutelyContinuousOnInterval_supportFn hK hne p q
  have hg := ac_supportFn_add hK hne (π / 2) p q
  have hh1 : AbsolutelyContinuousOnInterval (fun t => supportFn K t - 1) p q :=
    hh.fun_sub (ac_const 1 p q)
  have hg1 : AbsolutelyContinuousOnInterval (fun t => supportFn K (t + π / 2) - 1) p q :=
    hg.fun_sub (ac_const 1 p q)
  have hY := two_mul_curveJ_frame hh hg
  have hX := two_mul_curveJ_frame hh1 hg1
  have eY : outerCorner K = fun t => supportFn K t • u t + supportFn K (t + π / 2) • v t := rfl
  have eX : innerCorner K
      = fun t => (supportFn K t - 1) • u t + (supportFn K (t + π / 2) - 1) • v t := rfl
  rw [← eY] at hY
  rw [← eX] at hX
  simp only [deriv_sub_const] at hX
  -- integrability
  have hc := continuous_supportFn hK hne
  have hcg : Continuous fun t => supportFn K (t + π / 2) := hc.comp (continuous_add_const _)
  have i1 : IntervalIntegrable (fun t => supportFn K t ^ 2 + supportFn K (t + π / 2) ^ 2
      + supportFn K t * deriv (fun t => supportFn K (t + π / 2)) t
      - supportFn K (t + π / 2) * deriv (supportFn K) t) volume p q :=
    ((((hc.pow 2).intervalIntegrable p q).add ((hcg.pow 2).intervalIntegrable p q)).add
      (hg.intervalIntegrable_deriv.continuousOn_mul hc.continuousOn)).sub
      (hh.intervalIntegrable_deriv.continuousOn_mul hcg.continuousOn)
  have i2 : IntervalIntegrable (fun t => (supportFn K t - 1) ^ 2
      + (supportFn K (t + π / 2) - 1) ^ 2
      + (supportFn K t - 1) * deriv (fun t => supportFn K (t + π / 2)) t
      - (supportFn K (t + π / 2) - 1) * deriv (supportFn K) t) volume p q :=
    (((((hc.sub continuous_const).pow 2).intervalIntegrable p q).add
      (((hcg.sub continuous_const).pow 2).intervalIntegrable p q)).add
      (hg.intervalIntegrable_deriv.continuousOn_mul (hc.sub continuous_const).continuousOn)).sub
      (hh.intervalIntegrable_deriv.continuousOn_mul (hcg.sub continuous_const).continuousOn)
  have hdiff : (∫ t in p..q, (supportFn K t ^ 2 + supportFn K (t + π / 2) ^ 2
      + supportFn K t * deriv (fun t => supportFn K (t + π / 2)) t
      - supportFn K (t + π / 2) * deriv (supportFn K) t))
      - (∫ t in p..q, ((supportFn K t - 1) ^ 2 + (supportFn K (t + π / 2) - 1) ^ 2
      + (supportFn K t - 1) * deriv (fun t => supportFn K (t + π / 2)) t
      - (supportFn K (t + π / 2) - 1) * deriv (supportFn K) t))
      = ∫ t in p..q, (2 * (supportFn K t + supportFn K (t + π / 2) - 1)
          + (deriv (fun t => supportFn K (t + π / 2)) t - deriv (supportFn K) t)) := by
    rw [← intervalIntegral.integral_sub i1 i2]
    congr 1; funext t; ring
  have i3 : IntervalIntegrable (fun t => 2 * (supportFn K t + supportFn K (t + π / 2) - 1))
      volume p q := (((hc.add hcg).sub continuous_const).const_smul (2:ℝ)).intervalIntegrable p q
  have i4 : IntervalIntegrable
      (fun t => deriv (fun t => supportFn K (t + π / 2)) t - deriv (supportFn K) t) volume p q :=
    hg.intervalIntegrable_deriv.sub hh.intervalIntegrable_deriv
  rw [intervalIntegral.integral_add i3 i4, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hg.intervalIntegrable_deriv hh.intervalIntegrable_deriv,
    hg.integral_deriv_eq_sub, hh.integral_deriv_eq_sub] at hdiff
  linarith

end Sofa
