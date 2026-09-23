/-
# Sofa/Quadratic.lean — Baek §7.1: convex domains and quadratic functionals

Baek's Def 7.1.1 defines a *convex domain* as a space `V` with a barycentric operation `c_λ` that
embeds into a convex subset of a vector space.  Only three consequences of that definition are
ever used, so `ConvexDomain` below asks exactly for them: a carrier set closed under `c_λ` for
`λ ∈ [0,1]`, with `c_0(x,y) = x` and `c_1(x,y) = y`.  This is weaker than Baek's definition (it
does not demand an embedding) and therefore gives *stronger* theorems; and it applies verbatim
both to a convex subset of a vector space (`ConvexDomain.ofConvex`) and to the space of planar
convex bodies under Minkowski combination (`Sofa/Minkowski.lean`), which is not a vector space.

Contents: `ConvexLinearOn` (Def 7.1.2), `ConvexBilinearOn` (Def 7.1.3), `IsQuadraticOn`
(Def 7.1.4), the directional derivative `dirDeriv` (Def 7.1.5) with Lemma 7.1.4, and
**Theorem 7.1.5** (a concave quadratic functional is maximized exactly where its directional
derivative is nonpositive), plus `≡` (Def 7.1.7).

STATUS: [PROOF-C-local] round 1 (2026-09-18, Opus 5).
-/
import Mathlib

noncomputable section

open Set Filter Topology

namespace Sofa

variable {V W : Type*}

/-- **Def 7.1.1** (weakened): a set with a barycentric operation. -/
structure ConvexDomain (V : Type*) where
  /-- The underlying set. -/
  carrier : Set V
  /-- The barycentric operation `c_λ`. -/
  bary : ℝ → V → V → V
  mem : ∀ ⦃x⦄, x ∈ carrier → ∀ ⦃y⦄, y ∈ carrier → ∀ ⦃l : ℝ⦄, 0 ≤ l → l ≤ 1 →
    bary l x y ∈ carrier
  bary_zero : ∀ x ∈ carrier, ∀ y ∈ carrier, bary 0 x y = x
  bary_one : ∀ x ∈ carrier, ∀ y ∈ carrier, bary 1 x y = y

/-- A convex subset of a real vector space is a convex domain. -/
def ConvexDomain.ofConvex [AddCommGroup V] [Module ℝ V] {S : Set V} (hS : Convex ℝ S) :
    ConvexDomain V where
  carrier := S
  bary l x y := (1 - l) • x + l • y
  mem := by intro x hx y hy l hl0 hl1; exact hS hx hy (by linarith) hl0 (by ring)
  bary_zero x _ y _ := by simp
  bary_one x _ y _ := by simp

variable [AddCommGroup W] [Module ℝ W]

/-! ## Convex-linear and convex-bilinear maps -/

/-- **Def 7.1.2.** `f` preserves the barycentric operation. -/
def ConvexLinearOn (D : ConvexDomain V) (f : V → W) : Prop :=
  ∀ ⦃x⦄, x ∈ D.carrier → ∀ ⦃y⦄, y ∈ D.carrier → ∀ ⦃l : ℝ⦄, 0 ≤ l → l ≤ 1 →
    f (D.bary l x y) = (1 - l) • f x + l • f y

lemma ConvexLinearOn.const (D : ConvexDomain V) (w : W) : ConvexLinearOn D (fun _ => w) := by
  intro x _ y _ l _ _
  show w = (1 - l) • w + l • w
  rw [← add_smul]; simp

lemma ConvexLinearOn.add {D : ConvexDomain V} {f g : V → W} (hf : ConvexLinearOn D f)
    (hg : ConvexLinearOn D g) : ConvexLinearOn D (fun x => f x + g x) := by
  intro x hx y hy l hl0 hl1
  show f (D.bary l x y) + g (D.bary l x y) = (1 - l) • (f x + g x) + l • (f y + g y)
  rw [hf hx hy hl0 hl1, hg hx hy hl0 hl1, smul_add, smul_add]
  abel

lemma ConvexLinearOn.sub {D : ConvexDomain V} {f g : V → W} (hf : ConvexLinearOn D f)
    (hg : ConvexLinearOn D g) : ConvexLinearOn D (fun x => f x - g x) := by
  intro x hx y hy l hl0 hl1
  show f (D.bary l x y) - g (D.bary l x y) = (1 - l) • (f x - g x) + l • (f y - g y)
  rw [hf hx hy hl0 hl1, hg hx hy hl0 hl1, smul_sub, smul_sub]
  abel

lemma ConvexLinearOn.smul {D : ConvexDomain V} {f : V → W} (hf : ConvexLinearOn D f) (c : ℝ) :
    ConvexLinearOn D (fun x => c • f x) := by
  intro x hx y hy l hl0 hl1
  show c • f (D.bary l x y) = (1 - l) • (c • f x) + l • (c • f y)
  rw [hf hx hy hl0 hl1, smul_add, smul_comm c, smul_comm c]

omit [AddCommGroup W] [Module ℝ W] in
/-- Composition: if `f` maps `D` into `E` preserving the barycentric operation (Baek's
convex-linearity between convex domains) and `g` is convex-linear on `E`, then `g ∘ f` is
convex-linear on `D`.  When `E = ConvexDomain.ofConvex`, `hbary` *is* `ConvexLinearOn D f`. -/
lemma ConvexLinearOn.comp {U : Type*} [AddCommGroup U] [Module ℝ U] {D : ConvexDomain V}
    {E : ConvexDomain W} {f : V → W} {g : W → U}
    (hmap : ∀ x ∈ D.carrier, f x ∈ E.carrier)
    (hbary : ∀ ⦃x⦄, x ∈ D.carrier → ∀ ⦃y⦄, y ∈ D.carrier → ∀ ⦃l : ℝ⦄, 0 ≤ l → l ≤ 1 →
      f (D.bary l x y) = E.bary l (f x) (f y))
    (hg : ConvexLinearOn E g) : ConvexLinearOn D (fun x => g (f x)) := by
  intro x hx y hy l hl0 hl1
  show g (f (D.bary l x y)) = (1 - l) • g (f x) + l • g (f y)
  rw [hbary hx hy hl0 hl1, hg (hmap x hx) (hmap y hy) hl0 hl1]

/-- **Def 7.1.3.** -/
structure ConvexBilinearOn (D : ConvexDomain V) (g : V → V → ℝ) : Prop where
  right : ∀ x ∈ D.carrier, ConvexLinearOn D (g x)
  left : ∀ y ∈ D.carrier, ConvexLinearOn D (fun x => g x y)

/-- **Def 7.1.4.** -/
def IsQuadraticOn (D : ConvexDomain V) (f : V → ℝ) : Prop :=
  ∃ g : V → V → ℝ, ConvexBilinearOn D g ∧ ∀ x ∈ D.carrier, f x = g x x

/-! ## The quadratic expansion (7.1) -/

/-- Baek's Equation (7.1). -/
theorem ConvexBilinearOn.expand {D : ConvexDomain V} {g : V → V → ℝ}
    (hg : ConvexBilinearOn D g) {x y : V} (hx : x ∈ D.carrier) (hy : y ∈ D.carrier) {l : ℝ}
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    g (D.bary l x y) (D.bary l x y)
      = (1 - l) ^ 2 * g x x + l * (1 - l) * (g x y + g y x) + l ^ 2 * g y y := by
  have hmem : D.bary l x y ∈ D.carrier := D.mem hx hy hl0 hl1
  have e1 : g (D.bary l x y) (D.bary l x y)
      = (1 - l) • g x (D.bary l x y) + l • g y (D.bary l x y) := hg.left _ hmem hx hy hl0 hl1
  have e2 : g x (D.bary l x y) = (1 - l) • g x x + l • g x y := hg.right _ hx hx hy hl0 hl1
  have e3 : g y (D.bary l x y) = (1 - l) • g y x + l • g y y := hg.right _ hy hx hy hl0 hl1
  rw [e1, e2, e3]
  simp only [smul_eq_mul]
  ring

/-! ## The directional derivative (Def 7.1.5) -/

/-- **Def 7.1.5.** `Df(K; K') = d/dλ f(c_λ(K,K'))` at `λ = 0` (a right derivative). -/
def dirDeriv (D : ConvexDomain V) (f : V → ℝ) (K K' : V) : ℝ :=
  derivWithin (fun l : ℝ => f (D.bary l K K')) (Ici 0) 0

/-- The restriction of a quadratic functional to a `c_λ`-segment, in normalized form. -/
theorem quad_along {D : ConvexDomain V} {g : V → V → ℝ} (hg : ConvexBilinearOn D g)
    {f : V → ℝ} (hf : ∀ x ∈ D.carrier, f x = g x x) {K K' : V} (hK : K ∈ D.carrier)
    (hK' : K' ∈ D.carrier) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    f (D.bary l K K') = f K + (g K K' + g K' K - 2 * g K K) * l
      + (g K K + g K' K' - (g K K' + g K' K)) * l ^ 2 := by
  rw [hf _ (D.mem hK hK' hl0 hl1), hg.expand hK hK' hl0 hl1, hf K hK]
  ring

/-- **Lemma 7.1.4.** -/
theorem dirDeriv_eq {D : ConvexDomain V} {g : V → V → ℝ} (hg : ConvexBilinearOn D g)
    {f : V → ℝ} (hf : ∀ x ∈ D.carrier, f x = g x x) {K K' : V} (hK : K ∈ D.carrier)
    (hK' : K' ∈ D.carrier) :
    dirDeriv D f K K' = g K K' + g K' K - 2 * g K K := by
  set L := g K K' + g K' K - 2 * g K K with hL
  set Q := g K K + g K' K' - (g K K' + g K' K) with hQ
  set p : ℝ → ℝ := fun l => f K + L * l + Q * l ^ 2 with hp
  have hagree : ∀ l ∈ Icc (0 : ℝ) 1, f (D.bary l K K') = p l := fun l hl =>
    quad_along hg hf hK hK' hl.1 hl.2
  have hderiv : HasDerivAt p L 0 := by
    have h1 : HasDerivAt (fun l : ℝ => f K + L * l) L 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul L).const_add (f K)
    have h2 : HasDerivAt (fun l : ℝ => Q * l ^ 2) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℝ)).const_mul Q
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3
  have hwithin : HasDerivWithinAt (fun l : ℝ => f (D.bary l K K')) L (Ici 0) 0 := by
    refine (hderiv.hasDerivWithinAt (s := Ici (0 : ℝ))).congr_of_eventuallyEq ?_
      (hagree 0 ⟨le_rfl, zero_le_one⟩)
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by norm_num : (0:ℝ) < 1))]
      with l hl0 hl1
    exact hagree l ⟨hl0, hl1.le⟩
  rw [dirDeriv, hwithin.derivWithin (uniqueDiffWithinAt_Ici 0)]

/-! ## Theorem 7.1.5 -/

private lemma linear_coeff_nonpos {L Q : ℝ} (h : ∀ l : ℝ, 0 < l → l ≤ 1 → L * l + Q * l ^ 2 ≤ 0) :
    L ≤ 0 := by
  by_contra hc
  push Not at hc
  set l : ℝ := min 1 (L / (2 * (|Q| + 1))) with hl
  have hQ0 : (0 : ℝ) ≤ |Q| := abs_nonneg Q
  have hden : (0 : ℝ) < 2 * (|Q| + 1) := by linarith
  have hl0 : 0 < l := lt_min one_pos (div_pos hc hden)
  have hl1 : l ≤ 1 := min_le_left _ _
  have hlb : l ≤ L / (2 * (|Q| + 1)) := min_le_right _ _
  have hkey := h l hl0 hl1
  have hstep : L + Q * l ≤ 0 := by nlinarith [hkey, hl0]
  have hQl : |Q| * l ≤ L / 2 := by
    have h1 : |Q| * l ≤ |Q| * (L / (2 * (|Q| + 1))) := mul_le_mul_of_nonneg_left hlb hQ0
    have h2 : |Q| * (L / (2 * (|Q| + 1))) ≤ L / 2 := by
      rw [← mul_div_assoc, div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 2)]
      nlinarith [hc.le, hQ0]
    linarith
  have hlow : -(|Q| * l) ≤ Q * l := by
    have := neg_abs_le Q
    nlinarith [hl0.le, hQ0]
  linarith

/-- **Def 7.1.6.** -/
def ConcaveOnDomain (D : ConvexDomain V) (f : V → ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ D.carrier → ∀ ⦃y⦄, y ∈ D.carrier → ∀ ⦃l : ℝ⦄, 0 ≤ l → l ≤ 1 →
    (1 - l) * f x + l * f y ≤ f (D.bary l x y)

/-- **Theorem 7.1.5.** A concave quadratic functional is maximized at `K` exactly when its
directional derivative at `K` is nonpositive in every direction. -/
theorem isMaxOn_iff_dirDeriv_nonpos {D : ConvexDomain V} {g : V → V → ℝ}
    (hg : ConvexBilinearOn D g) {f : V → ℝ} (hf : ∀ x ∈ D.carrier, f x = g x x)
    (hconc : ConcaveOnDomain D f) {K : V} (hK : K ∈ D.carrier) :
    (∀ K' ∈ D.carrier, f K' ≤ f K) ↔ ∀ K' ∈ D.carrier, dirDeriv D f K K' ≤ 0 := by
  constructor
  · intro hmax K' hK'
    rw [dirDeriv_eq hg hf hK hK']
    refine linear_coeff_nonpos (Q := g K K + g K' K' - (g K K' + g K' K)) fun l hl0 hl1 => ?_
    have hq := quad_along hg hf hK hK' hl0.le hl1
    have hle := hmax _ (D.mem hK hK' hl0.le hl1)
    linarith [hq ▸ hle]
  · intro hder K' hK'
    have hL : g K K' + g K' K - 2 * g K K ≤ 0 := by
      rw [← dirDeriv_eq hg hf hK hK']; exact hder K' hK'
    have hhalf := quad_along hg hf hK hK' (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    have hone := quad_along hg hf hK hK' (by norm_num : (0:ℝ) ≤ 1) le_rfl
    rw [D.bary_one K hK K' hK'] at hone
    have hc := hconc hK hK' (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    rw [hhalf] at hc
    nlinarith [hone, hL, hc]

/-! ## Def 7.1.7: equality up to a convex-linear term -/

/-- **Def 7.1.7.** `f ≡_D g` iff `f − g` is convex-linear. -/
def EqUpToLinear (D : ConvexDomain V) (f g : V → ℝ) : Prop :=
  ConvexLinearOn D (fun x => f x - g x)

lemma EqUpToLinear.refl (D : ConvexDomain V) (f : V → ℝ) : EqUpToLinear D f f := by
  show ConvexLinearOn D (fun x => f x - f x)
  have he : (fun x : V => f x - f x) = fun _ : V => (0 : ℝ) := by funext x; ring
  rw [he]; exact ConvexLinearOn.const D 0

lemma EqUpToLinear.symm {D : ConvexDomain V} {f g : V → ℝ} (h : EqUpToLinear D f g) :
    EqUpToLinear D g f := by
  have h2 := (ConvexLinearOn.const D (0 : ℝ)).sub h
  show ConvexLinearOn D (fun x => g x - f x)
  have he : (fun x : V => g x - f x) = fun x : V => (0 : ℝ) - (f x - g x) := by funext x; ring
  rw [he]; exact h2

lemma EqUpToLinear.trans {D : ConvexDomain V} {f g k : V → ℝ} (h1 : EqUpToLinear D f g)
    (h2 : EqUpToLinear D g k) : EqUpToLinear D f k := by
  have h3 := h1.add h2
  show ConvexLinearOn D (fun x => f x - k x)
  have he : (fun x : V => f x - k x) = fun x : V => (f x - g x) + (g x - k x) := by funext x; ring
  rw [he]; exact h3
