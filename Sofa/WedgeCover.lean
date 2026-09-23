/-
# Sofa/WedgeCover.lean — the wedge decomposition of a convex body (step 5(d) of Thm 7.1.3)

Baek's Thm 7.1.3 states `|K| = ½ ∫ h_K dσ_K`.  `Sofa/AreaThm.lean` proves the *local* identity
`secR K a b = curveG K a b` for a short angular interval.  What remains is the **global
assembly**: that the sectors cut out by a fine partition of one full turn really tile `K`.

The obstruction is that a full turn is not a wedge, so the binary additivity `secR_add'` cannot
be iterated all the way round.  The fix used here is an *explicit lift of the argument*:

    `vtxAngle K t = t + arcsin (⟪v⁺_K(t), v_t⟫ / ‖v⁺_K(t)‖)`

satisfies `v⁺_K(t) = ‖v⁺_K(t)‖ • u (vtxAngle K t)` and `vtxAngle K (t+2π) = vtxAngle K t + 2π`
*on the nose* — no covering-space theory is needed, because `⟪v⁺_K(t), u_t⟫ = h_K(t) > 0` pins
the argument to the open half-turn around `t`.  With this lift the wedges become genuine angular
intervals `[θ_j, θ_{j+1}]` inside `[θ_0, θ_0 + 2π]`, and tiling is interval arithmetic.

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Sofa.VertexOrder

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace

namespace Sofa

variable {K : Set ℝ²}

/-! ## Polar form of a plane vector -/

/-- `u_α × u_β = sin (β − α)`. -/
lemma cross_u_u (α β : ℝ) : cross (u α) (u β) = sin (β - α) := by
  rw [cross, u_coord_zero, u_coord_one, u_coord_zero, u_coord_one, sin_sub]; ring

lemma cross_smul_smul' (r s : ℝ) (p q : ℝ²) :
    cross (r • p) (s • q) = r * s * cross p q := by
  rw [cross_smul_left, cross_smul_right]; ring

lemma sq_add_sq_of_norm_eq_one {z : ℝ²} (hz : ‖z‖ = 1) : z 0 ^ 2 + z 1 ^ 2 = 1 := by
  have h := real_inner_self_eq_norm_sq z
  rw [inner_eq, hz] at h
  linear_combination h

/-- Every unit vector of `ℝ²` is `u ψ` for some angle `ψ`. -/
lemma exists_angle {z : ℝ²} (hz : ‖z‖ = 1) : ∃ ψ : ℝ, u ψ = z := by
  have hsq := sq_add_sq_of_norm_eq_one hz
  have h0 : -1 ≤ z 0 := by nlinarith [sq_nonneg (z 1), sq_nonneg (z 0 + 1)]
  have h1 : z 0 ≤ 1 := by nlinarith [sq_nonneg (z 1), sq_nonneg (z 0 - 1)]
  have hroot : √(1 - z 0 ^ 2) = |z 1| := by
    rw [show (1 : ℝ) - z 0 ^ 2 = z 1 ^ 2 by linarith, Real.sqrt_sq_eq_abs]
  refine ⟨if 0 ≤ z 1 then arccos (z 0) else -arccos (z 0), ?_⟩
  split_ifs with hz1
  · have hc : cos (arccos (z 0)) = z 0 := Real.cos_arccos h0 h1
    have hs : sin (arccos (z 0)) = z 1 := by
      rw [Real.sin_arccos, hroot, abs_of_nonneg hz1]
    ext i; fin_cases i <;> simp [u, hc, hs]
  · push Not at hz1
    have hc : cos (-arccos (z 0)) = z 0 := by rw [Real.cos_neg]; exact Real.cos_arccos h0 h1
    have hs : sin (-arccos (z 0)) = z 1 := by
      rw [Real.sin_neg, Real.sin_arccos, hroot, abs_of_neg hz1]; ring
    ext i; fin_cases i <;> simp [u, hc, hs]

/-- Polar form: a nonzero vector is `‖q‖ • u θ`. -/
lemma exists_polar {q : ℝ²} (hq : q ≠ 0) : ∃ θ : ℝ, q = ‖q‖ • u θ := by
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 hq
  have hunit : ‖(‖q‖⁻¹ • q : ℝ²)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  obtain ⟨θ, hθ⟩ := exists_angle hunit
  exact ⟨θ, by rw [hθ, smul_inv_smul₀ hn]⟩

lemma u_add_int_mul_two_pi (θ : ℝ) (k : ℤ) : u (θ + k * (2 * π)) = u θ := by
  ext i
  fin_cases i <;>
    simp [u, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

/-- Polar form with the angle normalised to `[a, a + 2π)`. -/
lemma exists_polar_Ico {q : ℝ²} (hq : q ≠ 0) (a : ℝ) :
    ∃ θ : ℝ, a ≤ θ ∧ θ < a + 2 * π ∧ q = ‖q‖ • u θ := by
  obtain ⟨θ₀, hθ₀⟩ := exists_polar hq
  have hpi : (0 : ℝ) < 2 * π := by linarith [pi_pos]
  set k : ℤ := ⌈(a - θ₀) / (2 * π)⌉ with hk
  have hle : (a - θ₀) / (2 * π) ≤ (k : ℝ) := Int.le_ceil _
  have hlt : (k : ℝ) < (a - θ₀) / (2 * π) + 1 := Int.ceil_lt_add_one _
  refine ⟨θ₀ + (k : ℝ) * (2 * π), ?_, ?_, ?_⟩
  · have := (div_le_iff₀ hpi).1 hle; linarith
  · have : (k : ℝ) * (2 * π) < ((a - θ₀) / (2 * π) + 1) * (2 * π) :=
      mul_lt_mul_of_pos_right hlt hpi
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hpi), one_mul] at this
    linarith
  · rw [u_add_int_mul_two_pi]; exact hθ₀

/-! ## The angle sandwich -/

/-- If `sin x ≥ 0 ≥ sin (x − Δ)` with `0 < Δ`, `x < 2π` and `x − Δ > −2π`, then `0 ≤ x ≤ Δ`.
This is the whole content of "`q` lies in the wedge iff its argument lies in the angular
interval". -/
lemma sin_sandwich {x Δ : ℝ} (hΔ0 : 0 < Δ)
    (hx2 : x < 2 * π) (hy1 : -(2 * π) < x - Δ)
    (h1 : 0 ≤ sin x) (h2 : sin (x - Δ) ≤ 0) : 0 ≤ x ∧ x ≤ Δ := by
  have hpi := pi_pos
  have hxπ : x ≤ π := by
    by_contra hc
    push Not at hc
    have hs : 0 < sin (x - π) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi] at hs
    linarith
  have hx0 : 0 ≤ x := by
    by_contra hc
    push Not at hc
    rcases lt_or_ge (-π) x with hlt | hle
    · have hs : 0 < sin (-x) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      rw [Real.sin_neg] at hs
      linarith
    · have hs : 0 < sin (x - Δ + 2 * π) :=
        sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      rw [Real.sin_add_two_pi] at hs
      linarith
  refine ⟨hx0, ?_⟩
  by_contra hc
  push Not at hc
  have hs : 0 < sin (x - Δ) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  linarith

/-! ## The lifted argument of the vertex map -/

variable {hm R : ℝ}

lemma AreaSetup.norm_vtxP_le (h : AreaSetup K hm R) (t : ℝ) : ‖vtxP K t‖ ≤ R :=
  h.norm_le _ (vtxP_mem h.isCompact h.nonempty t)

lemma AreaSetup.norm_vtxP_pos (h : AreaSetup K hm R) (t : ℝ) : 0 < ‖vtxP K t‖ := by
  have h1 : hm ≤ ⟪vtxP K t, u t⟫ := by rw [inner_vtxP_u]; exact h.hm_le t
  have h2 : ⟪vtxP K t, u t⟫ ≤ ‖vtxP K t‖ * ‖u t‖ := real_inner_le_norm _ _
  rw [norm_u, mul_one] at h2
  linarith [h.hm_pos]

lemma AreaSetup.R_pos (h : AreaSetup K hm R) : 0 < R :=
  lt_of_lt_of_le (h.norm_vtxP_pos 0) (h.norm_vtxP_le 0)

/-- `u_{t+φ} = cos φ · u_t + sin φ · v_t`. -/
lemma u_add' (t φ : ℝ) : u (t + φ) = cos φ • u t + sin φ • v t := by
  ext i
  fin_cases i <;> simp [u, v, cos_add, sin_add] <;> ring

/-- The Pythagoras identity in the moving frame. -/
lemma inner_sq_add_inner_sq (p : ℝ²) (t : ℝ) : ⟪p, u t⟫ ^ 2 + ⟪p, v t⟫ ^ 2 = ‖p‖ ^ 2 := by
  have hn := real_inner_self_eq_norm_sq p
  rw [inner_eq] at hn
  rw [inner_eq, inner_eq, u_coord_zero, u_coord_one, v_coord_zero, v_coord_one]
  linear_combination hn + (p 0 ^ 2 + p 1 ^ 2) * cos_sq_add_sin_sq t

/-- **The lifted argument** of the vertex `v⁺_K(t)`: an explicit real number `θ` with
`v⁺_K(t) = ‖v⁺_K(t)‖ • u θ` and `|θ − t| < π/2`. -/
def vtxAngle (K : Set ℝ²) (t : ℝ) : ℝ := t + arcsin (⟪vtxP K t, v t⟫ / ‖vtxP K t‖)

lemma vtxAngle_add_two_pi (K : Set ℝ²) (t : ℝ) :
    vtxAngle K (t + 2 * π) = vtxAngle K t + 2 * π := by
  rw [vtxAngle, vtxAngle, vtxP_add_two_pi, v_add_two_pi]; ring

section Lift

variable (h : AreaSetup K hm R) (t : ℝ)

include h in
private lemma cos_arcsin_frame :
    cos (arcsin (⟪vtxP K t, v t⟫ / ‖vtxP K t‖)) = ⟪vtxP K t, u t⟫ / ‖vtxP K t‖ := by
  set p := vtxP K t with hp
  set n := ‖p‖ with hn
  have hn0 : 0 < n := h.norm_vtxP_pos t
  have ha : hm ≤ ⟪p, u t⟫ := by rw [hp, inner_vtxP_u]; exact h.hm_le t
  have ha0 : 0 < ⟪p, u t⟫ := lt_of_lt_of_le h.hm_pos ha
  have hpy : ⟪p, u t⟫ ^ 2 + ⟪p, v t⟫ ^ 2 = n ^ 2 := inner_sq_add_inner_sq p t
  rw [Real.cos_arcsin]
  rw [show (1 : ℝ) - (⟪p, v t⟫ / n) ^ 2 = (⟪p, u t⟫ / n) ^ 2 by field_simp; linarith]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

include h in
private lemma sin_arcsin_frame :
    sin (arcsin (⟪vtxP K t, v t⟫ / ‖vtxP K t‖)) = ⟪vtxP K t, v t⟫ / ‖vtxP K t‖ := by
  set p := vtxP K t with hp
  set n := ‖p‖ with hn
  have hn0 : 0 < n := h.norm_vtxP_pos t
  have hpy : ⟪p, u t⟫ ^ 2 + ⟪p, v t⟫ ^ 2 = n ^ 2 := inner_sq_add_inner_sq p t
  have hb : |⟪p, v t⟫| ≤ n := by
    rw [← Real.sqrt_sq_eq_abs, show n = √(n ^ 2) by rw [Real.sqrt_sq hn0.le]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (⟪p, u t⟫)])
  refine Real.sin_arcsin ?_ ?_
  · rw [le_div_iff₀ hn0]; cases abs_le.1 hb with | intro h1 h2 => linarith
  · rw [div_le_one hn0]; cases abs_le.1 hb with | intro h1 h2 => linarith

include h in
/-- **Polar form of the vertex** with the canonical lift. -/
theorem vtxP_eq_polar : vtxP K t = ‖vtxP K t‖ • u (vtxAngle K t) := by
  have hn0 : 0 < ‖vtxP K t‖ := h.norm_vtxP_pos t
  rw [vtxAngle, u_add', cos_arcsin_frame h t, sin_arcsin_frame h t, smul_add, smul_smul, smul_smul,
    mul_div_cancel₀ _ (ne_of_gt hn0), mul_div_cancel₀ _ (ne_of_gt hn0)]
  exact decomp_u_v t (vtxP K t)

include h in
lemma vtxAngle_sub_lt : vtxAngle K t - t < π / 2 := by
  have hn0 : 0 < ‖vtxP K t‖ := h.norm_vtxP_pos t
  have ha0 : 0 < ⟪vtxP K t, u t⟫ := by
    rw [inner_vtxP_u]; exact lt_of_lt_of_le h.hm_pos (h.hm_le t)
  have hc : 0 < cos (arcsin (⟪vtxP K t, v t⟫ / ‖vtxP K t‖)) := by
    rw [cos_arcsin_frame h t]; positivity
  have hle : arcsin (⟪vtxP K t, v t⟫ / ‖vtxP K t‖) ≤ π / 2 := Real.arcsin_le_pi_div_two _
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq, Real.cos_pi_div_two] at hc; exact absurd hc (lt_irrefl 0)
  · rw [vtxAngle]; linarith

include h in
lemma vtxAngle_sub_gt : hm / R - π / 2 < vtxAngle K t - t := by
  have hn0 : 0 < ‖vtxP K t‖ := h.norm_vtxP_pos t
  have hnR : ‖vtxP K t‖ ≤ R := h.norm_vtxP_le t
  have hR0 : 0 < R := h.R_pos
  have ha : hm ≤ ⟪vtxP K t, u t⟫ := by rw [inner_vtxP_u]; exact h.hm_le t
  set φ := arcsin (⟪vtxP K t, v t⟫ / ‖vtxP K t‖) with hφ
  have hc : cos φ = ⟪vtxP K t, u t⟫ / ‖vtxP K t‖ := cos_arcsin_frame h t
  have hcge : hm / R ≤ cos φ := by
    rw [hc, div_le_div_iff₀ hR0 hn0]
    nlinarith [h.hm_pos.le]
  have hge : -(π / 2) ≤ φ := Real.neg_pi_div_two_le_arcsin _
  have hpos : 0 < φ + π / 2 := by
    rcases eq_or_lt_of_le hge with heq | hlt
    · exfalso
      rw [← heq, Real.cos_neg, Real.cos_pi_div_two] at hcge
      have hpos : 0 < hm / R := div_pos h.hm_pos hR0
      linarith
    · linarith
  have hsin : sin (φ + π / 2) = cos φ := Real.sin_add_pi_div_two φ
  have hlt : sin (φ + π / 2) < φ + π / 2 := Real.sin_lt hpos
  rw [hsin] at hlt
  rw [vtxAngle]
  linarith

end Lift

lemma cross_vtxP_polar (h : AreaSetup K hm R) (s t : ℝ) :
    cross (vtxP K s) (vtxP K t)
      = ‖vtxP K s‖ * ‖vtxP K t‖ * sin (vtxAngle K t - vtxAngle K s) := by
  conv_lhs => rw [vtxP_eq_polar h s, vtxP_eq_polar h t]
  rw [cross_smul_smul', cross_u_u]

/-! ## One step of the partition: the angular increment lies in `[0, π)` -/

/-- `cross_vtxP_nonneg`, repackaged with the smallness hypothesis used everywhere else. -/
theorem cross_vtxP_nonneg_of (h : AreaSetup K hm R) {Sg : ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : b - a ≤ 1 / 2) (hσS : arcFn K b - arcFn K a ≤ Sg)
    (hsmall : 16 * (b - a) * (R + Sg + 1) ≤ hm) :
    0 ≤ cross (vtxP K a) (vtxP K b) := by
  have hpi := pi_gt_three
  have hσ0 : 0 ≤ arcFn K b - arcFn K a := by
    linarith [arcFn_mono h.isCompact h.nonempty hab]
  have hR0 := h.R_nonneg
  have htan : tan (b - a) ≤ 2 * (b - a) := tan_le_two_mul (by linarith) (by linarith)
  have htan0 : 0 ≤ tan (b - a) :=
    tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith)
  refine cross_vtxP_nonneg h.isCompact h.nonempty hab (by linarith) h.norm_le h.hm_pos
    (h.hm_le b) ?_
  calc tan (b - a) * (R + (arcFn K b - arcFn K a))
      ≤ (2 * (b - a)) * (R + Sg) := by
        apply mul_le_mul htan (by linarith) (by linarith) (by linarith)
    _ ≤ 16 * (b - a) * (R + Sg + 1) := by nlinarith
    _ ≤ hm := hsmall

/-- **The angular increment of one partition step** lies in `[0, π)`. -/
theorem vtxAngle_step (h : AreaSetup K hm R) {Sg : ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : b - a ≤ 1 / 2) (hσS : arcFn K b - arcFn K a ≤ Sg)
    (hsmall : 16 * (b - a) * (R + Sg + 1) ≤ hm) :
    0 ≤ vtxAngle K b - vtxAngle K a ∧ vtxAngle K b - vtxAngle K a < π := by
  have hpi := pi_gt_three
  have hR0 : 0 < R := h.R_pos
  have hm0 : 0 < hm := h.hm_pos
  have hσ0 : 0 ≤ arcFn K b - arcFn K a := by
    linarith [arcFn_mono h.isCompact h.nonempty hab]
  have hSg0 : 0 ≤ Sg := le_trans hσ0 hσS
  have hfa := vtxAngle_sub_gt h a
  have hfb := vtxAngle_sub_lt h b
  have hfa' := vtxAngle_sub_lt h a
  have hfb' := vtxAngle_sub_gt h b
  have hmR0 : 0 < hm / R := div_pos hm0 hR0
  -- the upper bound
  have hup : vtxAngle K b - vtxAngle K a < π := by
    have hd0 : 0 ≤ b - a := by linarith
    have hkey : (b - a) * R ≤ hm / 16 := by
      have h1 : (b - a) * R ≤ (b - a) * (R + Sg + 1) := by nlinarith
      nlinarith
    have hlt : (b - a) < hm / R := by
      rw [lt_div_iff₀ hR0]
      nlinarith
    linarith
  refine ⟨?_, hup⟩
  -- the lower bound, via `sin ≥ 0`
  have hlow : -π < vtxAngle K b - vtxAngle K a := by linarith
  have hcross := cross_vtxP_nonneg_of h hab hd hσS hsmall
  rw [cross_vtxP_polar h a b] at hcross
  have hna := h.norm_vtxP_pos a
  have hnb := h.norm_vtxP_pos b
  have hprod : 0 < ‖vtxP K a‖ * ‖vtxP K b‖ := mul_pos hna hnb
  have hsin : 0 ≤ sin (vtxAngle K b - vtxAngle K a) := by
    by_contra hc
    push Not at hc
    have := mul_neg_of_pos_of_neg hprod hc
    linarith
  by_contra hc
  push Not at hc
  have : 0 < sin (-(vtxAngle K b - vtxAngle K a)) :=
    sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [Real.sin_neg] at this
  linarith

/-! ## The tiling of `K` by the wedges of a partition -/

/-- The combinatorial data of a full-turn partition, expressed through the lifted argument. -/
structure PartData (K : Set ℝ²) (T : ℕ → ℝ) (N : ℕ) : Prop where
  pos : 0 < N
  mono : ∀ j < N, vtxAngle K (T j) ≤ vtxAngle K (T (j + 1))
  lt_pi : ∀ j < N, vtxAngle K (T (j + 1)) - vtxAngle K (T j) < π
  last : vtxAngle K (T N) = vtxAngle K (T 0) + 2 * π

namespace PartData

variable {T : ℕ → ℝ} {N : ℕ}

lemma mono' (hP : PartData K T N) {i j : ℕ} (hij : i ≤ j) (hjN : j ≤ N) :
    vtxAngle K (T i) ≤ vtxAngle K (T j) := by
  have step : ∀ d i : ℕ, i + d ≤ N → vtxAngle K (T i) ≤ vtxAngle K (T (i + d)) := by
    intro d
    induction d with
    | zero => intro i _; simp
    | succ n ih =>
      intro i hi
      have h1 : vtxAngle K (T i) ≤ vtxAngle K (T (i + n)) := ih i (by omega)
      have h2 : vtxAngle K (T (i + n)) ≤ vtxAngle K (T (i + n + 1)) := hP.mono (i + n) (by omega)
      have : i + (n + 1) = i + n + 1 := by omega
      rw [this]
      exact le_trans h1 h2
  have := step (j - i) i (by omega)
  rwa [show i + (j - i) = j by omega] at this

lemma le_last (hP : PartData K T N) {j : ℕ} (hj : j ≤ N) :
    vtxAngle K (T j) ≤ vtxAngle K (T 0) + 2 * π := by
  rw [← hP.last]; exact hP.mono' hj le_rfl

end PartData

/-- If `q` lies in the `m`-th wedge and is off every partition ray, then its argument lies in the
`m`-th angular interval. -/
theorem angle_mem_of_mem_wedgeC (h : AreaSetup K hm R) {T : ℕ → ℝ} {N : ℕ}
    (hP : PartData K T N) {m : ℕ} (hmN : m < N) {q : ℝ²} {θ : ℝ}
    (hθ1 : vtxAngle K (T 0) ≤ θ) (hθ2 : θ < vtxAngle K (T 0) + 2 * π)
    (hθ3 : q = ‖q‖ • u θ)
    (hoff : ∀ k, k ≤ N → cross (vtxP K (T k)) q ≠ 0)
    (hw : q ∈ wedgeC (vtxP K (T m)) (vtxP K (T (m + 1)))) :
    vtxAngle K (T m) ≤ θ ∧ θ ≤ vtxAngle K (T (m + 1)) := by
  have hq0 : q ≠ 0 := by
    intro hc; exact hoff 0 (Nat.zero_le _) (by rw [hc]; simp [cross])
  have hqn : 0 < ‖q‖ := norm_pos_iff.2 hq0
  have hnm : 0 < ‖vtxP K (T m)‖ := h.norm_vtxP_pos _
  have hnm1 : 0 < ‖vtxP K (T (m + 1))‖ := h.norm_vtxP_pos _
  -- turn the two wedge inequalities into statements about `sin`
  have e1 : cross (vtxP K (T m)) q = ‖vtxP K (T m)‖ * ‖q‖ * sin (θ - vtxAngle K (T m)) := by
    conv_lhs => rw [vtxP_eq_polar h (T m), hθ3]
    rw [cross_smul_smul', cross_u_u]
  have e2 : cross (vtxP K (T (m + 1))) q
      = ‖vtxP K (T (m + 1))‖ * ‖q‖ * sin (θ - vtxAngle K (T (m + 1))) := by
    conv_lhs => rw [vtxP_eq_polar h (T (m + 1)), hθ3]
    rw [cross_smul_smul', cross_u_u]
  have hp1 : 0 < ‖vtxP K (T m)‖ * ‖q‖ := mul_pos hnm hqn
  have hp2 : 0 < ‖vtxP K (T (m + 1))‖ * ‖q‖ := mul_pos hnm1 hqn
  have hs1 : 0 < sin (θ - vtxAngle K (T m)) := by
    rcases lt_trichotomy (sin (θ - vtxAngle K (T m))) 0 with hc | hc | hc
    · exact absurd (e1 ▸ hw.1) (not_le.2 (by
        have := mul_neg_of_pos_of_neg hp1 hc; linarith))
    · exact absurd (by rw [e1, hc, mul_zero] : cross (vtxP K (T m)) q = 0) (hoff m hmN.le)
    · exact hc
  have hs2 : sin (θ - vtxAngle K (T (m + 1))) < 0 := by
    rcases lt_trichotomy (sin (θ - vtxAngle K (T (m + 1)))) 0 with hc | hc | hc
    · exact hc
    · exact absurd (by rw [e2, hc, mul_zero] : cross (vtxP K (T (m + 1))) q = 0)
        (hoff (m + 1) (by omega))
    · exact absurd (e2 ▸ hw.2) (not_le.2 (by
        have := mul_pos hp2 hc; linarith))
  -- apply the sandwich
  have hΔ0 : 0 < vtxAngle K (T (m + 1)) - vtxAngle K (T m) := by
    rcases eq_or_lt_of_le (hP.mono m hmN) with heq | hlt
    · exfalso; rw [← heq] at hs2; linarith
    · linarith
  have hx2 : θ - vtxAngle K (T m) < 2 * π := by
    have := hP.mono' (Nat.zero_le m) hmN.le
    linarith
  have hy1 : -(2 * π) < θ - vtxAngle K (T m)
      - (vtxAngle K (T (m + 1)) - vtxAngle K (T m)) := by
    have hle := hP.le_last (show m + 1 ≤ N by omega)
    rcases eq_or_lt_of_le (show -(2 * π) ≤ θ - vtxAngle K (T (m + 1)) by linarith) with heq | hlt
    · exfalso
      rw [← heq] at hs2
      rw [show -(2 * π) = 0 - 2 * π by ring, Real.sin_sub_two_pi, Real.sin_zero] at hs2
      linarith
    · linarith
  obtain ⟨g1, g2⟩ := sin_sandwich hΔ0 hx2 hy1 hs1.le
    (by rw [show θ - vtxAngle K (T m) - (vtxAngle K (T (m + 1)) - vtxAngle K (T m))
      = θ - vtxAngle K (T (m + 1)) by ring]; exact hs2.le)
  exact ⟨by linarith, by linarith⟩

/-- **Covering.** Every nonzero point lies in one of the `N` wedges. -/
theorem exists_mem_wedgeC (h : AreaSetup K hm R) {T : ℕ → ℝ} {N : ℕ} (hP : PartData K T N)
    {q : ℝ²} (hq : q ≠ 0) :
    ∃ j, j < N ∧ q ∈ wedgeC (vtxP K (T j)) (vtxP K (T (j + 1))) := by
  classical
  obtain ⟨θ, hθ1, hθ2, hθ3⟩ := exists_polar_Ico hq (vtxAngle K (T 0))
  have hN := hP.pos
  have hex : ∃ j : ℕ, θ < vtxAngle K (T (j + 1)) := by
    refine ⟨N - 1, ?_⟩
    rw [show N - 1 + 1 = N from by omega, hP.last]
    exact hθ2
  set j := Nat.find hex with hjdef
  have hj1 : θ < vtxAngle K (T (j + 1)) := Nat.find_spec hex
  have hjlt : j < N := by
    have hle : Nat.find hex ≤ N - 1 := Nat.find_min' hex
      (by rw [show N - 1 + 1 = N from by omega, hP.last]; exact hθ2)
    omega
  have hj0 : vtxAngle K (T j) ≤ θ := by
    rcases Nat.eq_zero_or_pos j with hj | hj
    · rw [hj]; exact hθ1
    · have hmin : ¬ (θ < vtxAngle K (T (j - 1 + 1))) := Nat.find_min hex (by omega)
      push Not at hmin
      rwa [show j - 1 + 1 = j from by omega] at hmin
  have e1 : cross (vtxP K (T j)) q = ‖vtxP K (T j)‖ * ‖q‖ * sin (θ - vtxAngle K (T j)) := by
    conv_lhs => rw [vtxP_eq_polar h (T j), hθ3]
    rw [cross_smul_smul', cross_u_u]
  have e2 : cross (vtxP K (T (j + 1))) q
      = ‖vtxP K (T (j + 1))‖ * ‖q‖ * sin (θ - vtxAngle K (T (j + 1))) := by
    conv_lhs => rw [vtxP_eq_polar h (T (j + 1)), hθ3]
    rw [cross_smul_smul', cross_u_u]
  have hΔ := hP.lt_pi j hjlt
  have hmn := hP.mono j hjlt
  refine ⟨j, hjlt, ?_, ?_⟩
  · rw [e1]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
  · rw [e2]
    have hs : sin (θ - vtxAngle K (T (j + 1))) ≤ 0 := by
      have hpos : 0 < sin (-(θ - vtxAngle K (T (j + 1)))) :=
        sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      rw [Real.sin_neg] at hpos
      linarith
    have hnn := mul_nonneg (norm_nonneg (vtxP K (T (j + 1)))) (norm_nonneg q)
    nlinarith

/-- **The wedges tile `K`.** -/
theorem eq_iUnion_sector (h : AreaSetup K hm R) {T : ℕ → ℝ} {N : ℕ} (hP : PartData K T N) :
    K = ⋃ j ∈ Finset.range N, sector K (vtxP K (T j)) (vtxP K (T (j + 1))) := by
  refine Set.Subset.antisymm (fun q hqK => ?_) (Set.iUnion₂_subset fun j _ q hq => hq.1)
  rcases eq_or_ne q 0 with rfl | hq
  · exact Set.mem_biUnion (Finset.mem_range.2 hP.pos)
      ⟨hqK, by simp [cross], by simp [cross]⟩
  · obtain ⟨j, hj, hw⟩ := exists_mem_wedgeC h hP hq
    exact Set.mem_biUnion (Finset.mem_range.2 hj) ⟨hqK, hw⟩

/-! ## Almost-everywhere disjointness -/

/-- The union of the `N+1` partition rays is null. -/
theorem volume_rays_eq_zero (h : AreaSetup K hm R) {T : ℕ → ℝ} {N : ℕ} :
    volume (⋃ k ∈ Finset.range (N + 1), {q : ℝ² | cross (vtxP K (T k)) q = 0}) = 0 := by
  refine (measure_biUnion_null_iff ((Finset.range (N + 1)).finite_toSet.countable)).2 ?_
  exact fun k _ => volume_setOf_cross_eq_zero (h.vtxP_ne_zero _)

theorem sector_inter_subset_rays (h : AreaSetup K hm R) {T : ℕ → ℝ} {N : ℕ}
    (hP : PartData K T N) {i j : ℕ} (hi : i < N) (hj : j < N) (hij : i ≠ j) :
    sector K (vtxP K (T i)) (vtxP K (T (i + 1)))
        ∩ sector K (vtxP K (T j)) (vtxP K (T (j + 1)))
      ⊆ ⋃ k ∈ Finset.range (N + 1), {q : ℝ² | cross (vtxP K (T k)) q = 0} := by
  intro q hqq
  by_contra hc
  have hoff : ∀ k, k ≤ N → cross (vtxP K (T k)) q ≠ 0 := fun k hk hz =>
    hc (Set.mem_biUnion (Finset.mem_range.2 (by omega)) hz)
  have hq0 : q ≠ 0 := fun hz => hoff 0 (Nat.zero_le _) (by rw [hz]; simp [cross])
  obtain ⟨θ, hθ1, hθ2, hθ3⟩ := exists_polar_Ico hq0 (vtxAngle K (T 0))
  have hAi := angle_mem_of_mem_wedgeC h hP hi hθ1 hθ2 hθ3 hoff hqq.1.2
  have hAj := angle_mem_of_mem_wedgeC h hP hj hθ1 hθ2 hθ3 hoff hqq.2.2
  have key : ∀ a b : ℕ, a < b → b < N →
      (vtxAngle K (T a) ≤ θ ∧ θ ≤ vtxAngle K (T (a + 1))) →
      (vtxAngle K (T b) ≤ θ ∧ θ ≤ vtxAngle K (T (b + 1))) → False := by
    intro a b hab hbN h1 h2
    have hmid : vtxAngle K (T (a + 1)) ≤ vtxAngle K (T b) := hP.mono' (by omega) (by omega)
    have hθeq : θ = vtxAngle K (T (a + 1)) := le_antisymm h1.2 (le_trans hmid h2.1)
    refine hoff (a + 1) (by omega) ?_
    have e : cross (vtxP K (T (a + 1))) q
        = ‖vtxP K (T (a + 1))‖ * ‖q‖ * sin (θ - vtxAngle K (T (a + 1))) := by
      conv_lhs => rw [vtxP_eq_polar h (T (a + 1)), hθ3]
      rw [cross_smul_smul', cross_u_u]
    rw [e, hθeq, sub_self, Real.sin_zero, mul_zero]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact key i j hlt hj hAi hAj
  · exact key j i hgt hi hAj hAi

theorem sector_aeDisjoint (h : AreaSetup K hm R) {T : ℕ → ℝ} {N : ℕ}
    (hP : PartData K T N) {i j : ℕ} (hi : i < N) (hj : j < N) (hij : i ≠ j) :
    AEDisjoint volume (sector K (vtxP K (T i)) (vtxP K (T (i + 1))))
      (sector K (vtxP K (T j)) (vtxP K (T (j + 1)))) :=
  measure_mono_null (sector_inter_subset_rays h hP hi hj hij) (volume_rays_eq_zero h)

/-! ## The area of `K` as a sum of sector areas -/

theorem volume_eq_sum_sector (h : AreaSetup K hm R) {T : ℕ → ℝ} {N : ℕ} (hP : PartData K T N) :
    volume K = ∑ j ∈ Finset.range N, volume (sector K (vtxP K (T j)) (vtxP K (T (j + 1)))) := by
  conv_lhs => rw [eq_iUnion_sector h hP]
  refine measure_biUnion_finset₀ ?_ ?_
  · intro i hi j hj hij
    exact sector_aeDisjoint h hP (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij
  · intro j _
    exact (h.isCompact.measurableSet.inter (measurableSet_wedgeC _ _)).nullMeasurableSet

theorem volumeReal_eq_sum_secR (h : AreaSetup K hm R) {T : ℕ → ℝ} {N : ℕ} (hP : PartData K T N) :
    volume.real K = ∑ j ∈ Finset.range N, secR K (T j) (T (j + 1)) := by
  have hfin : volume K ≠ ⊤ := ne_of_lt h.isCompact.measure_lt_top
  have hsub : ∀ j : ℕ, volume (sector K (vtxP K (T j)) (vtxP K (T (j + 1)))) ≠ ⊤ :=
    fun j => ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      h.isCompact.measure_lt_top)
  rw [measureReal_def, volume_eq_sum_sector h hP, ENNReal.toReal_sum (fun j _ => hsub j)]
  rfl

/-! ## Theorem 7.1.3 for a body with the origin in its interior -/

lemma seq_mono_of_step {f : ℕ → ℝ} {N : ℕ} (hs : ∀ j < N, f j ≤ f (j + 1))
    {i j : ℕ} (hij : i ≤ j) (hjN : j ≤ N) : f i ≤ f j := by
  have step : ∀ d i : ℕ, i + d ≤ N → f i ≤ f (i + d) := by
    intro d
    induction d with
    | zero => intro i _; simp
    | succ n ih =>
      intro i hi
      have h1 : f i ≤ f (i + n) := ih i (by omega)
      have h2 : f (i + n) ≤ f (i + n + 1) := hs (i + n) (by omega)
      rw [show i + (n + 1) = i + n + 1 from by omega]
      exact le_trans h1 h2
  have := step (j - i) i (by omega)
  rwa [show i + (j - i) = j from by omega] at this

/-- **Theorem 7.1.3, partition form.** -/
theorem volumeReal_eq_curveG_of_part (h : AreaSetup K hm R) {T : ℕ → ℝ} {N : ℕ}
    (hP : PartData K T N) {Sg : ℝ}
    (hTmono : ∀ j < N, T j ≤ T (j + 1))
    (hTd : ∀ j < N, T (j + 1) - T j ≤ 1 / 2)
    (hTσ : ∀ j < N, arcFn K (T (j + 1)) - arcFn K (T j) ≤ Sg)
    (hTsmall : ∀ j < N, 16 * (T (j + 1) - T j) * (R + Sg + 1) ≤ hm) :
    volume.real K = curveG K (T 0) (T N) := by
  rw [volumeReal_eq_sum_secR h hP]
  rw [Finset.sum_congr rfl (fun j hj =>
    secR_eq_curveG h (hTmono j (Finset.mem_range.1 hj)) (hTd j (Finset.mem_range.1 hj))
      (hTσ j (Finset.mem_range.1 hj)) (hTsmall j (Finset.mem_range.1 hj)))]
  have tel : ∀ n, n ≤ N →
      ∑ j ∈ Finset.range n, curveG K (T j) (T (j + 1)) = curveG K (T 0) (T n) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [Finset.sum_range_zero, curveG, Set.Ioc_self, Measure.restrict_empty,
        integral_zero_measure, zero_div]
    | succ m ih =>
      intro hmN
      rw [Finset.sum_range_succ, ih (by omega),
        ← curveG_add h.isCompact h.nonempty
          (seq_mono_of_step hTmono (Nat.zero_le m) (by omega)) (hTmono m (by omega))]
  exact tel N le_rfl

/-- **Theorem 7.1.3** (Baek): for a convex body with the origin in its interior,
`|K| = ½ ∫_{(t₀, t₀+2π]} h_K dσ_K`. -/
theorem volumeReal_eq_curveG (h : AreaSetup K hm R) (t₀ : ℝ) :
    volume.real K = curveG K t₀ (t₀ + 2 * π) := by
  classical
  have hpi := pi_pos
  have hR0 := h.R_nonneg
  have hm0 := h.hm_pos
  set Sg := arcFn K (t₀ + 2 * π) - arcFn K t₀ with hSgdef
  have hSg0 : 0 ≤ Sg := by
    rw [hSgdef]
    linarith [arcFn_mono h.isCompact h.nonempty (show t₀ ≤ t₀ + 2 * π by linarith)]
  set N : ℕ := ⌈4 * π⌉₊ + ⌈32 * π * (R + Sg + 1) / hm⌉₊ + 1 with hNdef
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
  have hN4 : 4 * π ≤ (N : ℝ) := by
    have h1 : ((⌈4 * π⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (by omega : ⌈4 * π⌉₊ ≤ N)
    linarith [Nat.le_ceil (4 * π)]
  have hN32 : 32 * π * (R + Sg + 1) / hm ≤ (N : ℝ) := by
    have h1 : ((⌈32 * π * (R + Sg + 1) / hm⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (by omega : ⌈32 * π * (R + Sg + 1) / hm⌉₊ ≤ N)
    linarith [Nat.le_ceil (32 * π * (R + Sg + 1) / hm)]
  set w : ℝ := 2 * π / (N : ℝ) with hwdef
  have hw0 : 0 < w := by rw [hwdef]; positivity
  have hwN : (N : ℝ) * w = 2 * π := by
    rw [hwdef]; field_simp
  have hw2 : w ≤ 1 / 2 := by
    rw [hwdef, div_le_iff₀ hNR]; linarith
  have hwsmall : 16 * w * (R + Sg + 1) ≤ hm := by
    have hkey : 32 * π * (R + Sg + 1) ≤ hm * (N : ℝ) := by
      have := (div_le_iff₀ hm0).1 hN32
      linarith
    rw [hwdef]
    rw [div_le_iff₀ hNR] at *
    nlinarith [hkey]
  set T : ℕ → ℝ := fun j => t₀ + (j : ℝ) * w with hTdef
  have hT0 : T 0 = t₀ := by simp [hTdef]
  have hTN : T N = t₀ + 2 * π := by rw [hTdef]; simp only []; rw [hwN]
  have hTstep : ∀ j : ℕ, T (j + 1) - T j = w := by
    intro j; simp only [hTdef]; push_cast; ring
  have hTmono : ∀ j < N, T j ≤ T (j + 1) := by
    intro j _; have := hTstep j; linarith
  have hTle : ∀ j : ℕ, j ≤ N → t₀ ≤ T j ∧ T j ≤ t₀ + 2 * π := by
    intro j hj
    have hjR : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    constructor
    · simp only [hTdef]; nlinarith
    · simp only [hTdef]; nlinarith
  have hTσ : ∀ j < N, arcFn K (T (j + 1)) - arcFn K (T j) ≤ Sg := by
    intro j hj
    have h1 := (hTle j (by omega)).1
    have h2 := (hTle (j + 1) (by omega)).2
    have m1 := arcFn_mono h.isCompact h.nonempty h1
    have m2 := arcFn_mono h.isCompact h.nonempty h2
    rw [hSgdef]; linarith
  have hTd : ∀ j < N, T (j + 1) - T j ≤ 1 / 2 := by
    intro j _; rw [hTstep j]; exact hw2
  have hTsmall : ∀ j < N, 16 * (T (j + 1) - T j) * (R + Sg + 1) ≤ hm := by
    intro j _; rw [hTstep j]; exact hwsmall
  have hP : PartData K T N := by
    refine ⟨hNpos, fun j hj => ?_, fun j hj => ?_, ?_⟩
    · linarith [(vtxAngle_step h (hTmono j hj) (hTd j hj) (hTσ j hj) (hTsmall j hj)).1]
    · exact (vtxAngle_step h (hTmono j hj) (hTd j hj) (hTσ j hj) (hTsmall j hj)).2
    · rw [hTN, hT0, vtxAngle_add_two_pi]
  have := volumeReal_eq_curveG_of_part h hP hTmono hTd hTσ hTsmall
  rwa [hT0, hTN] at this
