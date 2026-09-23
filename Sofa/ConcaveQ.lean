/-
# Sofa/ConcaveQ.lean — Baek §8.2–§8.3: the upper bound `𝒬` and its concavity

Fix `φ ∈ (0, π/4)` (for Gerver's sofa `φ ≈ 0.039`), `φ^R = φ`, `φ^L = π/2 − φ`.

* **Def 8.2.2** `Qfun φ K B D = |K| + J(d_D) + J(Y_D, x^L_K) − J(x_K|[φ^R,φ^L]) + J(x^R_K, X_B) + J(b_B)`.
* **Def 8.3.4** `Pfun`, **Def 8.3.2** `Sfun` (four Mamikon regions of `K`), **Def 8.3.3** `Rfun`,
  `Lfun` (one Mamikon region of `B`, of `D`).
* **Lemma 8.3.4** (`Qfun_eq`): on the equalities of `𝓛`, `𝒬 = 𝒫_K − ℛ_B − ℒ_D`.
* **Lemma 8.3.7** (`Sfun_add_Pfun`): `𝒮_K + 𝒫_K = Λ(K)` with an *explicit* `Λ` (`Lamfun`) that is
  convex-linear in `K` (`Lamfun_mix`).  This holds for **every** cap of rotation angle `π/2` with
  nonempty interior — the atoms of `σ_K` at `0`, `φ`, `π/2 − φ`, `π/2`, `π` all cancel — so
  Chapter 8's concavity does not use the injectivity condition at all.
* **Theorem 8.3.8** (`Qfun_concave`): `𝒬` is concave along Minkowski combinations in `𝓛`.

Two corrections to the text, both harmless: in Def 8.3.3 `ℛ_B` must be `M_B(π + φ^R, 3π/2; l^{3π/2}_B)`
(the paper prints `π/2 + φ^R`; the proof of Lemma 8.3.4 only works with `π + φ^R`), and in the
proof of Lemma 8.3.7 the entry `J₄₂` equals `h_K(π)/2 − h_K(π)|e_K(π)|/2`, not `h_K(π/2)/2`.

STATUS: [PROOF-C-local] round 1 (2026-09-22, Opus 5.5).
-/
import Sofa.CapHalf
import Sofa.MamikonLine

noncomputable section

open Real Set Filter Topology MeasureTheory
open scoped EuclideanGeometry RealInnerProductSpace Interval

namespace Sofa

variable {K B D : Set ℝ²} {φ : ℝ}

/-! ## Segments on a line, and uniqueness of intersection points -/

/-- On a line `l(t, c)`, `J(p, q) = c · ⟪q − p, v_t⟫ / 2`. -/
lemma segJ_on_line {p q : ℝ²} {t c : ℝ} (hp : ⟪p, u t⟫ = c) (hq : ⟪q, u t⟫ = c) :
    segJ p q = c * ⟪q - p, v t⟫ / 2 := by
  refine segJ_of_line hp ?_
  have h1 := decomp_u_v t (q - p)
  rw [inner_sub_left, hq, hp, sub_self, zero_smul, zero_add] at h1
  rw [← h1]; abel

/-- Two points on the same two non-parallel lines coincide. -/
lemma eq_of_inner_u_eq_two {p q : ℝ²} {a b : ℝ} (hab : sin (b - a) ≠ 0)
    (ha : ⟪p, u a⟫ = ⟪q, u a⟫) (hb : ⟪p, u b⟫ = ⟪q, u b⟫) : p = q := by
  have hd := decomp_u_v a (p - q)
  rw [inner_sub_left, ha, sub_self, zero_smul, zero_add] at hd
  have h2 : ⟪p - q, u b⟫ = 0 := by rw [inner_sub_left, hb, sub_self]
  rw [hd, real_inner_smul_left, inner_v_u_eq_sin] at h2
  have h3 : ⟪p - q, v a⟫ = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd h hab
  rw [h3, zero_smul] at hd
  exact sub_eq_zero.1 hd

lemma inner_innerCorner_u_add (K : Set ℝ²) (t : ℝ) :
    ⟪innerCorner K t, u (t + π / 2)⟫ = supportFn K (t + π / 2) - 1 := by
  rw [innerCorner, u_add_pi_div_two, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_u_v, inner_v_v]; ring

lemma outerCorner_sub_innerCorner (K : Set ℝ²) (t : ℝ) :
    outerCorner K t = innerCorner K t + (u t + v t) := by
  rw [outerCorner, innerCorner, sub_smul, sub_smul, one_smul, one_smul]; abel

/-- `v_K(s, s + π/2)` is the outer corner `y_K(s)`. -/
lemma vtx2_add_pi_div_two (K : Set ℝ²) (s : ℝ) : vtx2 K s (s + π / 2) = outerCorner K s := by
  rw [vtx2, outerCorner, add_sub_cancel_left, cos_pi_div_two, sin_pi_div_two, mul_zero, sub_zero,
    div_one]

/-! ## The points and the functionals -/

/-- `W^R_K = b_K(φ) ∩ l(π/2, 0)`. -/
def ptWR (φ : ℝ) (K : Set ℝ²) : ℝ² := ((supportFn K φ - 1) / cos φ) • u 0

/-- `Z^L_K = d_K(φ^L) ∩ l(π/2, 0)`. -/
def ptZL (φ : ℝ) (K : Set ℝ²) : ℝ² := ((supportFn K (π - φ) - 1) / cos φ) • v (π / 2)

lemma ptWR_eq_wedgeW (φ : ℝ) (K : Set ℝ²) : ptWR φ K = wedgeW K φ := rfl

lemma ptZL_eq_wedgeZ (φ : ℝ) (K : Set ℝ²) : ptZL φ K = wedgeZ K (π / 2) (π / 2 - φ) := by
  rw [ptZL, wedgeZ, show π / 2 - φ + π / 2 = π - φ by ring, show π / 2 - (π / 2 - φ) = φ by ring]

/-- **Def 8.2.2** `𝒬(K, B, D)`. -/
def Qfun (φ : ℝ) (K B D : Set ℝ²) : ℝ :=
  volume.real K + convJ D (3 * π / 2) (2 * π - φ)
    + segJ (vtxM D (2 * π - φ)) (innerCorner K (π / 2 - φ))
    - curveJ (innerCorner K) φ (π / 2 - φ)
    + segJ (innerCorner K φ) (vtxP B (π + φ)) + convJ B (π + φ) (3 * π / 2)

/-- **Def 8.3.4** `𝒫_K`. -/
def Pfun (φ : ℝ) (K : Set ℝ²) : ℝ :=
  volume.real K + segJ (ptZL φ K) (innerCorner K (π / 2 - φ))
    - curveJ (innerCorner K) φ (π / 2 - φ) + segJ (innerCorner K φ) (ptWR φ K)

/-- **Def 8.3.3** `ℛ_B = M_B(π + φ^R, 3π/2; l^{3π/2}_B)` (the paper prints `π/2 + φ^R`). -/
def Rfun (φ : ℝ) (B : Set ℝ²) : ℝ := mamikonSeg B (π + φ) (3 * π / 2) (3 * π / 2)

/-- **Def 8.3.3** `ℒ_D = M_D(3π/2, 3π/2 + φ^L; l^{3π/2 + φ^L}_D)`. -/
def Lfun (φ : ℝ) (D : Set ℝ²) : ℝ := mamikonSeg D (3 * π / 2) (2 * π - φ) (2 * π - φ)

/-- **Def 8.3.2** `𝒮_K`: the four Mamikon regions of `K`. -/
def Sfun (φ : ℝ) (K : Set ℝ²) : ℝ :=
  mamikonSeg K 0 φ (π / 2) + mamikonM K φ (π / 2 - φ) (outerCorner K)
    + mamikonSeg K (π / 2 - φ) (π / 2) (π - φ) + mamikonSeg K (π / 2) π π

/-- The equalities (3) and (5) of Baek's Def 8.1.3 (all that §8.3 uses of `𝓛`). -/
structure LEq (φ : ℝ) (K B D : Set ℝ²) : Prop where
  B_phi : supportFn K φ + supportFn B (π + φ) = 1
  B_top : supportFn K (π / 2) + supportFn B (3 * π / 2) = 1
  D_top : supportFn K (π / 2) + supportFn D (3 * π / 2) = 1
  D_phi : supportFn K (π - φ) + supportFn D (2 * π - φ) = 1

/-! ## Lemma 8.3.4: `𝒬 = 𝒫_K − ℛ_B − ℒ_D` -/

/-- **Baek Lemma 8.3.4.** -/
theorem Qfun_eq (hK : IsCap K (π / 2)) (hL : LEq φ K B D) (hφ0 : 0 < φ) (hφ1 : φ < π / 4) :
    Qfun φ K B D = Pfun φ K - Rfun φ B - Lfun φ D := by
  have hpi := pi_pos
  have hcos : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hBtop : supportFn B (3 * π / 2) = 0 := by
    have := hL.B_top; rw [hK.supportFn_pi_div_two] at this; linarith
  have hDtop : supportFn D (3 * π / 2) = 0 := by
    have := hL.D_top; rw [hK.supportFn_pi_div_two] at this; linarith
  -- the lines
  have u3 : ∀ p : ℝ², ⟪p, u (3 * π / 2)⟫ = -⟪p, u (π / 2)⟫ := fun p => by
    rw [u_three_pi_div_two, inner_neg_right]
  have uπφ : ∀ p : ℝ², ⟪p, u (π + φ)⟫ = -⟪p, u φ⟫ := fun p => by
    rw [add_comm, u_add_pi, inner_neg_right]
  have u2πφ : ∀ p : ℝ², ⟪p, u (2 * π - φ)⟫ = -⟪p, u (π - φ)⟫ := fun p => by
    rw [show 2 * π - φ = (π - φ) + π by ring, u_add_pi, inner_neg_right]
  -- `W^R` and `Z^L` on the floor and on their inner walls
  have hWR0 : ⟪ptWR φ K, u (π / 2)⟫ = 0 := by
    rw [ptWR, real_inner_smul_left, inner_u_u_eq_cos, show (0:ℝ) - π / 2 = -(π / 2) by ring,
      cos_neg, cos_pi_div_two, mul_zero]
  have hWRφ : ⟪ptWR φ K, u φ⟫ = supportFn K φ - 1 := by
    rw [ptWR, real_inner_smul_left, inner_u_u_eq_cos, zero_sub, cos_neg]; field_simp
  have hZL0 : ⟪ptZL φ K, u (π / 2)⟫ = 0 := by
    rw [ptZL, real_inner_smul_left, inner_v_u]; ring
  have hZLφ : ⟪ptZL φ K, u (π - φ)⟫ = supportFn K (π - φ) - 1 := by
    rw [ptZL, real_inner_smul_left, inner_v_u_eq_sin, show π - φ - π / 2 = π / 2 - φ by ring,
      sin_pi_div_two_sub]; field_simp
  -- `x^R` and `x^L` on their inner walls
  have hxR : ⟪innerCorner K φ, u φ⟫ = supportFn K φ - 1 := inner_innerCorner_u (S := K) φ
  have hxL : ⟪innerCorner K (π / 2 - φ), u (π - φ)⟫ = supportFn K (π - φ) - 1 := by
    have := inner_innerCorner_u_add K (π / 2 - φ)
    rwa [show π / 2 - φ + π / 2 = π - φ by ring] at this
  -- `X_B` and `Y_D`
  have hXB : ⟪vtxP B (π + φ), u φ⟫ = supportFn K φ - 1 := by
    have h := inner_vtxP_u B (π + φ); rw [uπφ] at h; linarith [hL.B_phi]
  have hYD : ⟪vtxM D (2 * π - φ), u (π - φ)⟫ = supportFn K (π - φ) - 1 := by
    have h := inner_vtxM_u D (2 * π - φ); rw [u2πφ] at h; linarith [hL.D_phi]
  -- `W_B`, `Z_D` on the floor
  have hWB : ⟪vtxM B (3 * π / 2), u (π / 2)⟫ = 0 := by
    have h := inner_vtxM_u B (3 * π / 2); rw [u3, hBtop] at h; linarith
  have hZD : ⟪vtxP D (3 * π / 2), u (π / 2)⟫ = 0 := by
    have h := inner_vtxP_u D (3 * π / 2); rw [u3, hDtop] at h; linarith
  -- the corners of `l^{3π/2}_B` and `l^{2π−φ}_D` are `W^R_K` and `Z^L_K`
  have hVB : vtx2 B (π + φ) (3 * π / 2) = ptWR φ K := by
    refine eq_of_inner_u_eq_two (a := φ) (b := π / 2) ?_ ?_ ?_
    · rw [sin_pi_div_two_sub]; exact hcos.ne'
    · rw [hWRφ]
      have h := inner_vtx2_u_left B (π + φ) (3 * π / 2); rw [uπφ] at h; linarith [hL.B_phi]
    · rw [hWR0]
      have h := inner_vtx2_u_right B (a := π + φ) (b := 3 * π / 2) (by
        rw [show 3 * π / 2 - (π + φ) = π / 2 - φ by ring, sin_pi_div_two_sub]; exact hcos.ne')
      rw [u3, hBtop] at h; linarith
  have hVD : vtx2 D (3 * π / 2) (2 * π - φ) = ptZL φ K := by
    refine eq_of_inner_u_eq_two (a := π / 2) (b := π - φ) ?_ ?_ ?_
    · rw [show π - φ - π / 2 = π / 2 - φ by ring, sin_pi_div_two_sub]; exact hcos.ne'
    · rw [hZL0]
      have h := inner_vtx2_u_left D (3 * π / 2) (2 * π - φ); rw [u3, hDtop] at h; linarith
    · rw [hZLφ]
      have h := inner_vtx2_u_right D (a := 3 * π / 2) (b := 2 * π - φ) (by
        rw [show 2 * π - φ - 3 * π / 2 = π / 2 - φ by ring, sin_pi_div_two_sub]; exact hcos.ne')
      rw [u2πφ] at h; linarith [hL.D_phi]
  -- unfold `ℛ_B` and `ℒ_D`
  have hR : Rfun φ B = segJ (vtxP B (π + φ)) (ptWR φ K) + segJ (ptWR φ K) (vtxM B (3 * π / 2))
      - convJ B (π + φ) (3 * π / 2) := by
    rw [Rfun, mamikonSeg, lineCurve_of_lt (by linarith), lineCurve_self, hVB, segJ_self]; ring
  have hLD : Lfun φ D = segJ (vtxP D (3 * π / 2)) (ptZL φ K) + segJ (ptZL φ K) (vtxM D (2 * π - φ))
      - convJ D (3 * π / 2) (2 * π - φ) := by
    rw [Lfun, mamikonSeg, lineCurve_of_lt (by linarith), lineCurve_self, hVD, segJ_self]; ring
  -- the collinear triples and the floor
  have c1 : segJ (ptZL φ K) (vtxM D (2 * π - φ)) + segJ (vtxM D (2 * π - φ)) (innerCorner K (π / 2 - φ))
      = segJ (ptZL φ K) (innerCorner K (π / 2 - φ)) := by
    rw [segJ_on_line hZLφ hYD, segJ_on_line hYD hxL, segJ_on_line hZLφ hxL,
      inner_sub_left, inner_sub_left, inner_sub_left]; ring
  have c2 : segJ (innerCorner K φ) (vtxP B (π + φ)) + segJ (vtxP B (π + φ)) (ptWR φ K)
      = segJ (innerCorner K φ) (ptWR φ K) := by
    rw [segJ_on_line hxR hXB, segJ_on_line hXB hWRφ, segJ_on_line hxR hWRφ,
      inner_sub_left, inner_sub_left, inner_sub_left]; ring
  have f1 : segJ (ptWR φ K) (vtxM B (3 * π / 2)) = 0 := segJ_eq_zero_of_line_zero hWR0 hWB
  have f2 : segJ (vtxP D (3 * π / 2)) (ptZL φ K) = 0 := segJ_eq_zero_of_line_zero hZD hZL0
  rw [Qfun, Pfun, hR, hLD, f1, f2]
  linarith

/-! ## Lemma 8.3.7: `𝒮_K + 𝒫_K = Λ(K)` -/

/-- `v_K(φ, π/2) − W^R_K = ((1 − sin φ)/cos φ, 1)`. -/
def cvecR (φ : ℝ) : ℝ² := ((1 - sin φ) / cos φ) • u 0 + u (π / 2)

/-- `v_K(π/2, π − φ) − Z^L_K = ((sin φ − 1)/cos φ, 1)`. -/
def cvecL (φ : ℝ) : ℝ² := ((sin φ - 1) / cos φ) • u 0 + u (π / 2)

lemma vtx2_phi_eq (hK : IsCap K (π / 2)) (hcos : cos φ ≠ 0) :
    vtx2 K φ (π / 2) = ptWR φ K + cvecR φ := by
  have h1 := hK.supportFn_pi_div_two
  have hs := sin_sq_add_cos_sq φ
  ext i; fin_cases i
  · simp [vtx2, ptWR, cvecR, u, v, sin_pi_div_two_sub, cos_pi_div_two_sub, h1]
    field_simp
    linear_combination (supportFn K φ) * hs
  · simp [vtx2, ptWR, cvecR, u, v, sin_pi_div_two_sub, cos_pi_div_two_sub, h1]
    field_simp
    ring

lemma vtx2_pi_sub_phi_eq (hK : IsCap K (π / 2)) (hcos : cos φ ≠ 0) :
    vtx2 K (π / 2) (π - φ) = ptZL φ K + cvecL φ := by
  have h1 := hK.supportFn_pi_div_two
  have e : π - φ - π / 2 = π / 2 - φ := by ring
  ext i; fin_cases i
  · simp [vtx2, ptZL, cvecL, u, v, e, sin_pi_div_two_sub, cos_pi_div_two_sub, h1]
    field_simp
    ring
  · simp [vtx2, ptZL, cvecL, u, v, e, sin_pi_div_two_sub, cos_pi_div_two_sub, h1]

/-- **The convex-linear functional `Λ` of Baek's Lemma 8.3.7**, written out. -/
def Lamfun (φ : ℝ) (K : Set ℝ²) : ℝ :=
  supportFn K 0 / 2
  + ((vtx2 K 0 (π / 2)) 0 - (vtx2 K φ (π / 2)) 0) / 2
  + (cross (ptWR φ K) (u φ + v φ) + cross (cvecR φ) (innerCorner K φ)
      + cross (cvecR φ) (u φ + v φ)) / 2
  + ((∫ t in φ..(π / 2 - φ), (supportFn K t + supportFn K (t + π / 2) - 1))
      + ((supportFn K (π / 2 - φ + π / 2) - supportFn K (π / 2 - φ))
        - (supportFn K (φ + π / 2) - supportFn K φ)) / 2)
  + (cross (innerCorner K (π / 2 - φ)) (cvecL φ)
      + cross (u (π / 2 - φ) + v (π / 2 - φ)) (ptZL φ K)
      + cross (u (π / 2 - φ) + v (π / 2 - φ)) (cvecL φ)) / 2
  + ((vtx2 K (π / 2) (π - φ)) 0 - (vtx2 K (π / 2) π) 0) / 2
  + supportFn K π / 2

/-- `J(p, q) = (p₀ − q₀)/2` for two points on the top line `y = 1`. -/
lemma segJ_top {p q : ℝ²} (hp : ⟪p, u (π / 2)⟫ = 1) (hq : ⟪q, u (π / 2)⟫ = 1) :
    segJ p q = (p 0 - q 0) / 2 := by
  rw [segJ_on_line hp hq, v_pi_div_two, inner_neg_right, inner_sub_left, inner_u_zero,
    inner_u_zero]; ring

/-- **Baek Lemma 8.3.7**: `𝒮_K + 𝒫_K = Λ(K)`, for every cap with rotation angle `π/2` and
nonempty interior. -/
theorem Sfun_add_Pfun (hK : IsCap K (π / 2)) (hint : (interior K).Nonempty) (hφ0 : 0 < φ)
    (hφ1 : φ < π / 4) : Sfun φ K + Pfun φ K = Lamfun φ K := by
  have hpi := pi_pos
  have hKc := hK.isCompact
  have hne := hK.nonempty
  have hcos : 0 < cos φ := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hh2 : supportFn K (π / 2) = 1 := hK.supportFn_pi_div_two
  have hsinne : ∀ s, 0 ≤ s → s < π / 2 → sin (π / 2 - s) ≠ 0 := fun s h0 h1 =>
    (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
  -- the four rows
  have hQ1 : vtx2 K (π / 2 - φ) (π - φ) = outerCorner K (π / 2 - φ) := by
    have := vtx2_add_pi_div_two K (π / 2 - φ)
    rwa [show π / 2 - φ + π / 2 = π - φ by ring] at this
  have r1 : mamikonSeg K 0 φ (π / 2) = segJ (vtxP K 0) (vtx2 K 0 (π / 2))
      + segJ (vtx2 K 0 (π / 2)) (vtx2 K φ (π / 2)) + segJ (vtx2 K φ (π / 2)) (vtxM K φ)
      - convJ K 0 φ := by
    rw [mamikonSeg, lineCurve_of_lt (by linarith), lineCurve_of_lt (by linarith)]
  have r3 : mamikonSeg K (π / 2 - φ) (π / 2) (π - φ)
      = segJ (vtxP K (π / 2 - φ)) (outerCorner K (π / 2 - φ))
      + segJ (outerCorner K (π / 2 - φ)) (vtx2 K (π / 2) (π - φ))
      + segJ (vtx2 K (π / 2) (π - φ)) (vtxM K (π / 2)) - convJ K (π / 2 - φ) (π / 2) := by
    rw [mamikonSeg, lineCurve_of_lt (by linarith), lineCurve_of_lt (by linarith), hQ1]
  have r4 : mamikonSeg K (π / 2) π π = segJ (vtxP K (π / 2)) (vtx2 K (π / 2) π)
      + segJ (vtx2 K (π / 2) π) (vtxM K π) - convJ K (π / 2) π := by
    rw [mamikonSeg, lineCurve_of_lt (by linarith), lineCurve_self, segJ_self]; ring
  -- `|K|` through the convex arcs
  have hV := volumeReal_cap hK hint
  have hc1 := convJ_concat hKc hne (a := 0) (b := φ) (c := π) hφ0 (by linarith)
  have hc2 := convJ_concat hKc hne (a := φ) (b := π / 2 - φ) (c := π) (by linarith)
    (by linarith)
  have hc3 := convJ_concat hKc hne (a := π / 2 - φ) (b := π / 2) (c := π) (by linarith)
    (by linarith)
  -- (i) the right floor corner
  have b1 : segJ (vtxP K 0) (vtx2 K 0 (π / 2)) + supportFn K 0 * edgeLength K 0 / 2
      = supportFn K 0 / 2 := by
    have hv : ⟪vtx2 K 0 (π / 2), v 0⟫ = 1 := by
      rw [vtx2_eq_tanCurve, inner_tanCurve_v, lineW, hh2, sub_zero, cos_pi_div_two, sin_pi_div_two]
      ring
    rw [segJ_on_line (inner_vtxP_u K 0) (inner_vtx2_u_left K 0 (π / 2)), inner_sub_left, hv,
      inner_vtxP_v, hK.edgeMax_zero]
    ring
  -- (ii) the top line between `v_K(0, π/2)` and `v_K(φ, π/2)`
  have top : ∀ s, s < π / 2 → 0 ≤ s → ⟪vtx2 K s (π / 2), u (π / 2)⟫ = 1 := fun s hs hs0 => by
    rw [inner_vtx2_u_right K (hsinne s hs0 hs), hh2]
  have b2 : segJ (vtx2 K 0 (π / 2)) (vtx2 K φ (π / 2))
      = ((vtx2 K 0 (π / 2)) 0 - (vtx2 K φ (π / 2)) 0) / 2 :=
    segJ_top (top 0 (by linarith) le_rfl) (top φ (by linarith) hφ0.le)
  -- (iii) the line `l_K(φ)`, then the constant offsets (Lemma 8.3.6 (2))
  have hPφ : ⟪vtx2 K φ (π / 2), u φ⟫ = supportFn K φ := inner_vtx2_u_left K φ (π / 2)
  have b3 : segJ (vtx2 K φ (π / 2)) (vtxM K φ) + segJ (vtxM K φ) (vtxP K φ)
      + segJ (vtxP K φ) (outerCorner K φ) = segJ (vtx2 K φ (π / 2)) (outerCorner K φ) := by
    rw [segJ_on_line hPφ (inner_vtxM_u K φ), segJ_on_line (inner_vtxM_u K φ) (inner_vtxP_u K φ),
      segJ_on_line (inner_vtxP_u K φ) (inner_outerCorner_u K φ),
      segJ_on_line hPφ (inner_outerCorner_u K φ)]
    simp only [inner_sub_left]; ring
  have b3' : segJ (vtx2 K φ (π / 2)) (outerCorner K φ) + segJ (innerCorner K φ) (ptWR φ K)
      = (cross (ptWR φ K) (u φ + v φ) + cross (cvecR φ) (innerCorner K φ)
        + cross (cvecR φ) (u φ + v φ)) / 2 := by
    rw [vtx2_phi_eq hK hcos.ne', outerCorner_sub_innerCorner]
    simp only [segJ, cross_add_left, cross_add_right]
    rw [cross_comm (innerCorner K φ) (ptWR φ K)]
    ring
  -- (iv) the core curve (Lemma 8.3.6 (1))
  have b4 := curveJ_outer_sub_inner hKc hne φ (π / 2 - φ)
  -- (v) the line `l_K(π/2 − φ)` back and forth
  have b5 : segJ (outerCorner K (π / 2 - φ)) (vtxM K (π / 2 - φ))
      + segJ (vtxM K (π / 2 - φ)) (vtxP K (π / 2 - φ))
      + segJ (vtxP K (π / 2 - φ)) (outerCorner K (π / 2 - φ)) = 0 := by
    rw [segJ_on_line (inner_outerCorner_u K _) (inner_vtxM_u K _),
      segJ_on_line (inner_vtxM_u K _) (inner_vtxP_u K _),
      segJ_on_line (inner_vtxP_u K _) (inner_outerCorner_u K _)]
    simp only [inner_sub_left]; ring
  -- (vi) the constant offsets on the left (Lemma 8.3.6 (3))
  have b6 : segJ (outerCorner K (π / 2 - φ)) (vtx2 K (π / 2) (π - φ))
      + segJ (ptZL φ K) (innerCorner K (π / 2 - φ))
      = (cross (innerCorner K (π / 2 - φ)) (cvecL φ)
        + cross (u (π / 2 - φ) + v (π / 2 - φ)) (ptZL φ K)
        + cross (u (π / 2 - φ) + v (π / 2 - φ)) (cvecL φ)) / 2 := by
    rw [vtx2_pi_sub_phi_eq hK hcos.ne', outerCorner_sub_innerCorner]
    simp only [segJ, cross_add_left, cross_add_right]
    rw [cross_comm (ptZL φ K) (innerCorner K (π / 2 - φ))]
    ring
  -- (vii) the top line on the left
  have hQ2 : ⟪vtx2 K (π / 2) (π - φ), u (π / 2)⟫ = 1 := by
    rw [inner_vtx2_u_left, hh2]
  have hR1 : ⟪vtx2 K (π / 2) π, u (π / 2)⟫ = 1 := by rw [inner_vtx2_u_left, hh2]
  have hM2 : ⟪vtxM K (π / 2), u (π / 2)⟫ = 1 := by rw [inner_vtxM_u, hh2]
  have hP2 : ⟪vtxP K (π / 2), u (π / 2)⟫ = 1 := by rw [inner_vtxP_u, hh2]
  have b7 : segJ (vtx2 K (π / 2) (π - φ)) (vtxM K (π / 2)) + segJ (vtxM K (π / 2)) (vtxP K (π / 2))
      + segJ (vtxP K (π / 2)) (vtx2 K (π / 2) π)
      = ((vtx2 K (π / 2) (π - φ)) 0 - (vtx2 K (π / 2) π) 0) / 2 := by
    rw [segJ_top hQ2 hM2, segJ_top hM2 hP2, segJ_top hP2 hR1]; ring
  -- (viii) the left floor corner
  have b8 : segJ (vtx2 K (π / 2) π) (vtxM K π) + supportFn K π * edgeLength K π / 2
      = supportFn K π / 2 := by
    have hu : ⟪vtx2 K (π / 2) π, u π⟫ = supportFn K π :=
      inner_vtx2_u_right K (by rw [show π - π / 2 = π / 2 by ring, sin_pi_div_two]; norm_num)
    have hv : ⟪vtx2 K (π / 2) π, v π⟫ = -1 := by
      rw [inner_vtx2_v_right, hh2, show π / 2 - π = -(π / 2) by ring, sin_neg, sin_pi_div_two,
        show π - π / 2 = π / 2 by ring, cos_pi_div_two]; ring
    rw [segJ_on_line hu (inner_vtxM_u K π), inner_sub_left, hv, inner_vtxM_v, hK.edgeMin_pi]
    ring
  -- assemble
  have hP : Pfun φ K = volume.real K + segJ (ptZL φ K) (innerCorner K (π / 2 - φ))
      - curveJ (innerCorner K) φ (π / 2 - φ) + segJ (innerCorner K φ) (ptWR φ K) := rfl
  have hS : Sfun φ K = mamikonSeg K 0 φ (π / 2) + mamikonM K φ (π / 2 - φ) (outerCorner K)
      + mamikonSeg K (π / 2 - φ) (π / 2) (π - φ) + mamikonSeg K (π / 2) π π := rfl
  have r2 : mamikonM K φ (π / 2 - φ) (outerCorner K) = segJ (vtxP K φ) (outerCorner K φ)
      + curveJ (outerCorner K) φ (π / 2 - φ)
      + segJ (outerCorner K (π / 2 - φ)) (vtxM K (π / 2 - φ)) - convJ K φ (π / 2 - φ) := rfl
  rw [hS, hP, r1, r2, r3, r4, Lamfun]
  linarith

/-! ## `Λ` is convex-linear -/

lemma innerCorner_mix {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (t : ℝ) :
    innerCorner (mix l A B) t = (1 - l) • innerCorner A t + l • innerCorner B t := by
  rw [innerCorner, innerCorner, innerCorner, supportFn_mix hA hAne hB hBne hl0 hl1,
    supportFn_mix hA hAne hB hBne hl0 hl1]
  module

lemma ptWR_mix {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (φ : ℝ) :
    ptWR φ (mix l A B) = (1 - l) • ptWR φ A + l • ptWR φ B := by
  rw [ptWR, ptWR, ptWR, supportFn_mix hA hAne hB hBne hl0 hl1, smul_smul, smul_smul, ← add_smul]
  congr 1
  rcases eq_or_ne (cos φ) 0 with h | h
  · rw [h, div_zero, div_zero, div_zero]; ring
  · field_simp; ring

lemma ptZL_mix {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (φ : ℝ) :
    ptZL φ (mix l A B) = (1 - l) • ptZL φ A + l • ptZL φ B := by
  rw [ptZL, ptZL, ptZL, supportFn_mix hA hAne hB hBne hl0 hl1, smul_smul, smul_smul, ← add_smul]
  congr 1
  rcases eq_or_ne (cos φ) 0 with h | h
  · rw [h, div_zero, div_zero, div_zero]; ring
  · field_simp; ring

/-- `Λ` is convex-linear in `K` (for any compact nonempty bodies). -/
theorem Lamfun_mix {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (φ : ℝ) :
    Lamfun φ (mix l A B) = (1 - l) * Lamfun φ A + l * Lamfun φ B := by
  have hsf := fun t => supportFn_mix hA hAne hB hBne hl0 hl1 t
  have hint : ∫ t in φ..(π / 2 - φ), (supportFn (mix l A B) t + supportFn (mix l A B) (t + π / 2) - 1)
      = (1 - l) * (∫ t in φ..(π / 2 - φ), (supportFn A t + supportFn A (t + π / 2) - 1))
        + l * ∫ t in φ..(π / 2 - φ), (supportFn B t + supportFn B (t + π / 2) - 1) := by
    have hcA : Continuous fun t => supportFn A t + supportFn A (t + π / 2) - 1 :=
      ((continuous_supportFn hA hAne).add ((continuous_supportFn hA hAne).comp
        (continuous_add_const _))).sub continuous_const
    have hcB : Continuous fun t => supportFn B t + supportFn B (t + π / 2) - 1 :=
      ((continuous_supportFn hB hBne).add ((continuous_supportFn hB hBne).comp
        (continuous_add_const _))).sub continuous_const
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hcA.intervalIntegrable _ _).const_mul _)
        ((hcB.intervalIntegrable _ _).const_mul _)]
    congr 1; funext t; rw [hsf, hsf]; ring
  rw [Lamfun, Lamfun, Lamfun, hint, vtx2_mix hA hAne hB hBne hl0 hl1,
    vtx2_mix hA hAne hB hBne hl0 hl1, vtx2_mix hA hAne hB hBne hl0 hl1,
    vtx2_mix hA hAne hB hBne hl0 hl1, ptWR_mix hA hAne hB hBne hl0 hl1,
    ptZL_mix hA hAne hB hBne hl0 hl1, innerCorner_mix hA hAne hB hBne hl0 hl1,
    innerCorner_mix hA hAne hB hBne hl0 hl1]
  simp only [hsf, cross_add_left, cross_add_right, cross_smul_left, cross_smul_right,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-! ## The Mamikon functionals are convex -/

theorem Sfun_mix_le {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hφ0 : 0 < φ) (hφ1 : φ < π / 4) :
    Sfun φ (mix l A B) ≤ (1 - l) * Sfun φ A + l * Sfun φ B := by
  have hpi := pi_pos
  have h1 := mamikonSeg_mix_le hA hAne hB hBne hl0 hl1 (a := 0) (b := φ) (t := π / 2) hφ0
    (by linarith) (by linarith)
  have h2 := mamikonM_outerCorner_mix_le hA hAne hB hBne hl0 hl1 (a := φ) (b := π / 2 - φ)
    (by linarith)
  have h3 := mamikonSeg_mix_le hA hAne hB hBne hl0 hl1 (a := π / 2 - φ) (b := π / 2)
    (t := π - φ) (by linarith) (by linarith) (by linarith)
  have h4 := mamikonSeg_mix_le_self hA hAne hB hBne hl0 hl1 (a := π / 2) (t := π) (by linarith)
    (by linarith)
  rw [Sfun, Sfun, Sfun]
  linarith

theorem Rfun_mix_le {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hφ0 : 0 < φ) (hφ1 : φ < π / 4) :
    Rfun φ (mix l A B) ≤ (1 - l) * Rfun φ A + l * Rfun φ B :=
  mamikonSeg_mix_le_self hA hAne hB hBne hl0 hl1 (by linarith [pi_pos]) (by linarith [pi_pos])

theorem Lfun_mix_le {A B : Set ℝ²} (hA : IsCompact A) (hAne : A.Nonempty) (hB : IsCompact B)
    (hBne : B.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hφ0 : 0 < φ) (hφ1 : φ < π / 4) :
    Lfun φ (mix l A B) ≤ (1 - l) * Lfun φ A + l * Lfun φ B :=
  mamikonSeg_mix_le_self hA hAne hB hBne hl0 hl1 (by linarith [pi_pos]) (by linarith [pi_pos])

/-! ## Theorem 8.3.8 -/

lemma LEq.mix {K₁ B₁ D₁ K₂ B₂ D₂ : Set ℝ²} (hK₁ : IsCompact K₁) (hK₁ne : K₁.Nonempty)
    (hK₂ : IsCompact K₂) (hK₂ne : K₂.Nonempty) (hB₁ : IsCompact B₁) (hB₁ne : B₁.Nonempty)
    (hB₂ : IsCompact B₂) (hB₂ne : B₂.Nonempty) (hD₁ : IsCompact D₁) (hD₁ne : D₁.Nonempty)
    (hD₂ : IsCompact D₂) (hD₂ne : D₂.Nonempty) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (h₁ : LEq φ K₁ B₁ D₁) (h₂ : LEq φ K₂ B₂ D₂) :
    LEq φ (mix l K₁ K₂) (mix l B₁ B₂) (mix l D₁ D₂) := by
  have sK := fun t => supportFn_mix hK₁ hK₁ne hK₂ hK₂ne hl0 hl1 t
  have sB := fun t => supportFn_mix hB₁ hB₁ne hB₂ hB₂ne hl0 hl1 t
  have sD := fun t => supportFn_mix hD₁ hD₁ne hD₂ hD₂ne hl0 hl1 t
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sK, sB]; linear_combination (1 - l) * h₁.B_phi + l * h₂.B_phi
  · rw [sK, sB]; linear_combination (1 - l) * h₁.B_top + l * h₂.B_top
  · rw [sK, sD]; linear_combination (1 - l) * h₁.D_top + l * h₂.D_top
  · rw [sK, sD]; linear_combination (1 - l) * h₁.D_phi + l * h₂.D_phi

/-- **`𝒬 = Λ − 𝒮 − ℛ − ℒ`** on the equalities of `𝓛`. -/
theorem Qfun_eq_Lam (hK : IsCap K (π / 2)) (hint : (interior K).Nonempty) (hL : LEq φ K B D)
    (hφ0 : 0 < φ) (hφ1 : φ < π / 4) :
    Qfun φ K B D = Lamfun φ K - Sfun φ K - Rfun φ B - Lfun φ D := by
  rw [Qfun_eq hK hL hφ0 hφ1, ← Sfun_add_Pfun hK hint hφ0 hφ1]; ring

/-- **Baek Theorem 8.3.8**: `𝒬` is concave along Minkowski combinations of triples satisfying the
equalities of `𝓛`, with `K` a cap of rotation angle `π/2` with nonempty interior and `B`, `D`
compact and nonempty. -/
theorem Qfun_concave {K₁ B₁ D₁ K₂ B₂ D₂ : Set ℝ²} (hφ0 : 0 < φ) (hφ1 : φ < π / 4)
    (hK₁ : IsCap K₁ (π / 2)) (hK₂ : IsCap K₂ (π / 2)) (hi₁ : (interior K₁).Nonempty)
    (hi₂ : (interior K₂).Nonempty) (hB₁ : IsCompact B₁) (hB₁ne : B₁.Nonempty) (hB₂ : IsCompact B₂)
    (hB₂ne : B₂.Nonempty) (hD₁ : IsCompact D₁) (hD₁ne : D₁.Nonempty) (hD₂ : IsCompact D₂)
    (hD₂ne : D₂.Nonempty) (hL₁ : LEq φ K₁ B₁ D₁) (hL₂ : LEq φ K₂ B₂ D₂) {l : ℝ} (hl0 : 0 ≤ l)
    (hl1 : l ≤ 1) :
    (1 - l) * Qfun φ K₁ B₁ D₁ + l * Qfun φ K₂ B₂ D₂
      ≤ Qfun φ (mix l K₁ K₂) (mix l B₁ B₂) (mix l D₁ D₂) := by
  have hKc₁ := hK₁.isCompact
  have hKc₂ := hK₂.isCompact
  have hK₁ne := hK₁.nonempty
  have hK₂ne := hK₂.nonempty
  have hKl := isCap_mix hK₁ hK₂ hl0 hl1
  have hil := interior_mix_nonempty hi₁ hi₂ hl0 hl1
  have hLl := LEq.mix hKc₁ hK₁ne hKc₂ hK₂ne hB₁ hB₁ne hB₂ hB₂ne hD₁ hD₁ne hD₂ hD₂ne hl0 hl1 hL₁ hL₂
  rw [Qfun_eq_Lam hK₁ hi₁ hL₁ hφ0 hφ1, Qfun_eq_Lam hK₂ hi₂ hL₂ hφ0 hφ1,
    Qfun_eq_Lam hKl hil hLl hφ0 hφ1, Lamfun_mix hKc₁ hK₁ne hKc₂ hK₂ne hl0 hl1]
  have hS := Sfun_mix_le hKc₁ hK₁ne hKc₂ hK₂ne hl0 hl1 hφ0 hφ1
  have hR := Rfun_mix_le hB₁ hB₁ne hB₂ hB₂ne hl0 hl1 hφ0 hφ1
  have hLD := Lfun_mix_le hD₁ hD₁ne hD₂ hD₂ne hl0 hl1 hφ0 hφ1
  linarith

end Sofa
