/-
# Sofa/Main.lean — the final assembly (Baek, proof of Thm 1.1.1, p.110)

The main theorem `sofaConstant ≤ volume gerversSofa` is derived here from three **interface
theorems**, which are exactly what Chapters 3–8 of Baek's paper have to deliver:

* **(I1)** (Ch.3: Thm 3.5.2, 3.5.4, 3.5.5) balanced maximum caps exist, contain their niche, and
  maximize `A_ω` among all caps — **proved** in `Sofa/BalancedMax.lean`;
* **(I2)** (Ch.4: Thm 1.5.2) for `ω ∈ [arccos(5/11), π/2)` with `A_ω(K_ω) ≥ 2.2`, the balanced
  maximum sofa `S_ω` is dominated by a monotone sofa of rotation angle `π/2` — **proved** in
  `Sofa/Thm152.lean`;
* **(I3)** (Ch.5–8) `A_{π/2}(K) ≤ |G|` for balanced maximum caps — **derived** here
  (`IsBalancedMaxCap.sofaArea_le_gerver`) from Thm 6.1.1, Thm 8.1.8, Thm 8.2.4 (all proved) and
* **(I3′)** `gerver_Qfun_le` (Cor 8.5.8 + Thm 8.4.6): `𝒬_φ ≤ |G|` on the domain `𝓛_φ`, for
  Gerver's `φ ∈ (0, 1/25]` — **derived** from the concavity of `𝒬` (Thm 8.3.8), its directional
  derivative (Thm 8.5.6, `Sofa/DirDerivQ.lean`), Thm 8.5.7 (`Sofa/QMax.lean`) and
* **(I3″)** `gerver_data` (Baek §8.4): the cap `K = C(G)` of the upstream `G = gerversSofa` (a
  monotone sofa of rotation angle `π/2` with `I(G) = G`: `Sofa.GP.isMonotoneSofa_gerversSofa`)
  and the explicit tails `B`, `D` of its niche satisfy `GerverNicheFacts` — Thm 8.4.1 (2), the
  description of the niche, which Baek does not prove — **proved** in `Sofa/GerverArch.lean` and
  `Sofa/GerverNiche.lean`.  Also **proved** for `K`, `B`, `D`: `|K| ≥ 2.2`, Thm 6.1.2
  (`Sofa.GP.isInjectiveCap_Kg`), Thm 8.4.1 (1), (3), (4) and Romik's ODEs (Thm 8.4.2,
  `Sofa.GP.gerverODE_Kg`).  Everything Baek derives from them is **proved**: Thm 8.4.3
  (`Sofa/GerverFaces.lean`), Prop 8.4.4 and Thm 8.4.5 (`Sofa/GerverODE.lean`), Thm 8.4.6
  `𝒬(K, B_K, D_K) = A(K)` (`Sofa/GerverArea.lean`).

Everything else in the reduction — Thm 1.5.1, the monotone hull (Ch.2), Thm 2.5.9–2.5.10, and the
Hammersley lower bound used to handle sofas of area `< 2.2` — is already proved (no `sorry`).

STATUS: [PROOF-C] [AXIOM-CHECK] round 41 (2026-09-23, Opus 5.5).  **No `sorry`**: the main theorems
`sofaConstant_le_volume_gerversSofa` and `sofaConstant_eq_volume_gerversSofa'` depend only on
`propext`, `Classical.choice` and `Quot.sound`.  History: the assembly `Interfaces.sofaConstant_le`
(for an arbitrary target set `G`) has been `sorry`-free from the start; round 37 proved the upstream
`ABφθSpec.existsUnique` (so the upstream *definition* of `gerversSofa` is axiom-clean); round 38
proved that Gerver's sofa is a moving sofa and a monotone sofa with `I(G) = G`
(`Sofa/GerverConn.lean`, `Sofa/GerverMono.lean`); rounds 39–40 proved Romik's ODEs, Thm 8.4.1 (1),
(3), (4), `|K| ≥ 2.2` and Thm 6.1.2 for the cap `K = C(G)` and the explicit tails `B`, `D`; round 41
proved Thm 8.4.1 (2), the description of the niche (`Sofa/GerverArch.lean`,
`Sofa/GerverNiche.lean`).  The upstream statement `isMovingSofa_gerversSofa` keeps its `sorry` (the
upstream file cannot import the downstream proof `Sofa.GP.isMovingSofa_gerversSofa'`); it is not used.
-/
import Sofa.GerverArea
import Sofa.GerverNiche
import Sofa.GerverTailDeriv
import Sofa.HammersleyArea
import Sofa.RotationBound
import Sofa.Thm152

noncomputable section

open Real Set Filter Topology MeasureTheory MovingSofa
open scoped EuclideanGeometry RealInnerProductSpace unitInterval

namespace Sofa

variable {K : Set ℝ²} {ω : ℝ}

/-! ## The remaining interface theorems

(I1a) `exists_isBalancedMaxCap` (Thm 3.5.2), (I1b) `IsBalancedMaxCap.niche_subset` (Thm 3.5.4)
and (I1c) `IsBalancedMaxCap.isMax` (Thm 3.5.5) are **proved** in `Sofa/BalancedMax.lean`;
(I2) `IsBalancedMaxCap.exists_monotoneSofa_pi_div_two` (Thm 1.5.2) in `Sofa/Thm152.lean`. -/

lemma IsMonotoneSofa.volume_ne_top {T : Set ℝ²} (hT : IsMonotoneSofa T ω) (hω0 : 0 < ω)
    (hω1 : ω ≤ π / 2) : volume T ≠ ⊤ :=
  (hT.isSofaWithAngle hω0 hω1).isCompact.measure_lt_top.ne

/-- Baek's Thm 8.4.1 (2) (the description of the niche) for a cap `K` and two tails `B`, `D`: the
fields of `GerverNiche` other than those proved separately for `K = C(G)` and the explicit tails
`B = p₁ u + p₁' v`, `D = −p₂' u + p₂ v` (`Sofa.GP.Bg`, `Sofa.GP.Dg`): `GerverAngles` (`Sofa.GC.gerver_angles`), `N(K) ⊆ K`
(`niche_Ccap_gerversSofa_subset`), `|K| ≥ 2.2` (`Sofa.GP.area_Kg`), the walls and the continuity
of the tails (`Sofa.GP.Bg_wall`, `Sofa.GP.Dg_wall`, `Sofa.GP.continuous_Bg`,
`Sofa.GP.continuous_Dg`), the end points `B(π/2 − θ) = x_K(φ)`, `D(θ) = x_K(π/2 − φ)`
(`Sofa.GP.Bg_start`, `Sofa.GP.Dg_end`) and the one-sided derivatives of the tails (Thm 8.4.1 (4),
`Sofa.GP.Bg_deriv`, `Sofa.GP.Dg_deriv`), and Thm 6.1.2 (`K` is injective, `Sofa.GP.isInjectiveCap_Kg`).
For Gerver's sofa these facts are proved in `gerver_data`.  See `GerverTails` and `GerverNiche` for
the meaning of the fields. -/
structure GerverNicheFacts (φ θ : ℝ) (K : Set ℝ²) (Bc Dc : ℝ → ℝ²) : Prop where
  B_closure : ∀ t ∈ Ioo (π / 2 - θ) (π / 2), Bc t ∈ closure (niche K (π / 2))
  B_not_mem : ∀ t ∈ Ioo (π / 2 - θ) (π / 2), Bc t ∉ niche K (π / 2)
  D_closure : ∀ t ∈ Ioo 0 θ, Dc t ∈ closure (niche K (π / 2))
  D_not_mem : ∀ t ∈ Ioo 0 θ, Dc t ∉ niche K (π / 2)
  core_closure : ∀ t ∈ Icc φ (π / 2 - φ), innerCorner K t ∈ closure (niche K (π / 2))
  below : ∀ q ∈ niche K (π / 2),
    (∃ t ∈ Icc 0 θ, Dc t 0 = q 0 ∧ q 1 < Dc t 1) ∨
    (∃ t ∈ Icc φ (π / 2 - φ), innerCorner K t 0 = q 0 ∧ q 1 < innerCorner K t 1) ∨
    (∃ t ∈ Icc (π / 2 - θ) (π / 2), Bc t 0 = q 0 ∧ q 1 < Bc t 1)

/-- `GerverNicheFacts` and the proved fields give `GerverNiche`. -/
lemma GerverNicheFacts.toGerverNiche {φ θ : ℝ} {Bc Dc : ℝ → ℝ²}
    (h : GerverNicheFacts φ θ K Bc Dc) (hA : GerverAngles φ θ) (hI : IsInjectiveCap K)
    (hN : niche K (π / 2) ⊆ K) (harea : 11 / 5 ≤ volume.real K)
    (hBw : ∀ t ∈ Icc (π / 2 - θ) (π / 2), ⟪Bc t, u t⟫ = supportFn K t - 1)
    (hDw : ∀ t ∈ Icc 0 θ, ⟪Dc t, u (t + π / 2)⟫ = supportFn K (t + π / 2) - 1)
    (hBc : ContinuousOn Bc (Icc (π / 2 - θ) (π / 2))) (hDc : ContinuousOn Dc (Icc 0 θ))
    (hBs : Bc (π / 2 - θ) = innerCorner K φ) (hDe : Dc θ = innerCorner K (π / 2 - φ))
    (hBd : ∃ β : ℝ → ℝ, ∀ t ∈ Ico (π / 2 - θ) (π / 2),
      β t < 0 ∧ HasDerivWithinAt Bc (β t • v t) (Ici t) t)
    (hDd : ∃ δ : ℝ → ℝ, ∀ t ∈ Ico 0 θ, 0 < δ t ∧ HasDerivWithinAt Dc (δ t • u t) (Ici t) t) :
    GerverNiche φ θ K Bc Dc :=
  { toGerverAngles := hA
    injective := hI
    niche_subset := hN
    area := harea
    B_closure := h.B_closure
    B_not_mem := h.B_not_mem
    D_closure := h.D_closure
    D_not_mem := h.D_not_mem
    B_start := hBs
    D_end := hDe
    B_wall := hBw
    D_wall := hDw
    B_cont := hBc
    D_cont := hDc
    B_deriv := hBd
    D_deriv := hDd
    core_closure := h.core_closure
    below := h.below }

/-- The cap of Gerver's sofa contains its niche (Thm 2.5.9: it is the cap of a monotone sofa). -/
theorem niche_Ccap_gerversSofa_subset :
    niche (Ccap gerversSofa (π / 2)) (π / 2) ⊆ Ccap gerversSofa (π / 2) := by
  have hpi := pi_pos
  have hT := Sofa.GP.isMonotoneSofa_gerversSofa
  exact ((hT.isCap_Ccap (by positivity) le_rfl).niche_subset_iff (by positivity) le_rfl).2
    ⟨_, hT, rfl⟩

/-- `A(C(G)) = |G|` (Thm 2.5.10 for the monotone sofa `G`). -/
theorem ofReal_sofaArea_Ccap_gerversSofa :
    ENNReal.ofReal (sofaArea (Ccap gerversSofa (π / 2)) (π / 2)) = volume gerversSofa := by
  have hpi := pi_pos
  have hT := Sofa.GP.isMonotoneSofa_gerversSofa
  rw [hT.sofaArea_Ccap (by positivity) le_rfl,
    ENNReal.ofReal_toReal (hT.volume_ne_top (by positivity) le_rfl)]

/-- **(I3″)** Baek §8.4 (Gerver's sofa): the cap `K = C(G)` of the upstream `G = gerversSofa` and
the explicit tails `B = p₁ u + p₁' v`, `D = −p₂' u + p₂ v` of its niche (the envelopes of the inner
walls; `Sofa.GP.Bg`, `Sofa.GP.Dg`) satisfy `GerverNicheFacts`, i.e. **Thm 8.4.1 (2)**: the tails
and the core lie in the closure of `N(K)`, the tails do not lie in `N(K)`, and every point of `N(K)`
lies strictly below a point of the arch `D ∪ x_K ∪ B` (`Sofa/GerverNiche.lean`; the key fact, that
no inner quadrant reaches the arch, is `Sofa/GerverArch.lean`).  Baek does not prove Thm 8.4.1
(Rem 8.4.1); together with Thm 6.1.2 (`Sofa.GP.isInjectiveCap_Kg`), `|K| ≥ 2.2`
(`Sofa.GP.area_Kg`), Thm 8.4.1 (1), (3), (4) and Romik's ODEs (`Sofa.GP.gerverODE_Kg`) it is
everything about Gerver's sofa that the proof uses. -/
theorem gerver_data : GerverNicheFacts MovingSofa.GerversSofa.φ MovingSofa.GerversSofa.θ
    (Ccap gerversSofa (π / 2)) Sofa.GP.Bg Sofa.GP.Dg where
  B_closure _ ht := Sofa.GP.Bg_mem_closure ht
  B_not_mem _ ht := Sofa.GP.Bg_not_mem_niche ht
  D_closure _ ht := Sofa.GP.Dg_mem_closure ht
  D_not_mem _ ht := Sofa.GP.Dg_not_mem_niche ht
  core_closure _ ht := Sofa.GP.innerCorner_mem_closure ht
  below _ hq := Sofa.GP.niche_below hq

/-- **(I3′)** Cor 8.5.8 + Thm 8.4.6: `𝒬_φ ≤ |G|` on the whole domain `𝓛_φ` (Def 8.1.3, `InL`) —
derived from (I3″) and Romik's ODEs (`Sofa.GP.gerverODE_Kg`): Thm 8.4.3 and Thm 8.4.5 give
`GerverData` (`GerverODE.gerverData`), Gerver's triple maximizes `𝒬` on `𝓛` (`GerverData.Qfun_le`:
Thm 8.5.7 with Thm 8.5.6, the concavity Thm 8.3.8 and Thm 7.1.5), and
`𝒬(K, B_K, D_K) ≤ A(K) = |G|` (Thm 8.4.6, `GerverNiche.Qfun_le_sofaArea`, with Thm 2.5.10 for the
monotone sofa `G`). -/
theorem gerver_Qfun_le : 0 < MovingSofa.GerversSofa.φ ∧ MovingSofa.GerversSofa.φ ≤ 1 / 25 ∧
    ∀ K B D : Set ℝ², InL MovingSofa.GerversSofa.φ K B D →
      ENNReal.ofReal (Qfun MovingSofa.GerversSofa.φ K B D) ≤ volume gerversSofa := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := Sofa.GC.gerver_angles
  have hpi := pi_pos
  have hN := gerver_data.toGerverNiche ⟨ha1, ha2, ha3, ha4⟩ Sofa.GP.isInjectiveCap_Kg
    niche_Ccap_gerversSofa_subset Sofa.GP.area_Kg (fun t ht => Sofa.GP.Bg_wall ⟨by linarith [ht.1], ht.2⟩)
    (fun t ht => Sofa.GP.Dg_wall ⟨ht.1, by linarith [ht.2]⟩)
    Sofa.GP.continuous_Bg.continuousOn Sofa.GP.continuous_Dg.continuousOn Sofa.GP.Bg_start
    Sofa.GP.Dg_end Sofa.GP.Bg_deriv Sofa.GP.Dg_deriv
  have hG := Sofa.GP.gerverODE_Kg.gerverData hN.toGerverTails
  have hQ : ENNReal.ofReal (Qfun MovingSofa.GerversSofa.φ (Ccap gerversSofa (π / 2))
      (Bset MovingSofa.GerversSofa.φ (Ccap gerversSofa (π / 2)))
      (Dset MovingSofa.GerversSofa.φ (Ccap gerversSofa (π / 2)))) ≤ volume gerversSofa := by
    rw [← ofReal_sofaArea_Ccap_gerversSofa]
    exact ENNReal.ofReal_le_ofReal hN.Qfun_le_sofaArea
  exact ⟨hG.phi_pos, hN.toGerverTails.phi_le, fun K' B' D' hP' =>
    (ENNReal.ofReal_le_ofReal (hG.Qfun_le hP')).trans hQ⟩

/-! ## Assembly (conditional on the interface, axiom-clean) -/

/-- The interface that Chapters 3–8 must deliver (only the parts used by the assembly), for a
target set `G` (Gerver's sofa).  The parameter `G` kept the conditional theorem free of the
upstream `sorry` that the *definition* of `gerversSofa` carried until round 37 (through
`ABφθSpec.existsUnique`, now proved). -/
structure Interfaces (G : Set ℝ²) : Prop where
  /-- (I1a) Thm 3.5.2 -/
  exists_bmc : ∀ ω : ℝ, 0 < ω → ω ≤ π / 2 → ∃ K, IsBalancedMaxCap K ω
  /-- (I1c) Thm 3.5.5 -/
  isMax : ∀ (K : Set ℝ²) (ω : ℝ), IsBalancedMaxCap K ω → 0 < ω → ω ≤ π / 2 →
    ∀ K' : Set ℝ², IsCap K' ω → sofaArea K' ω ≤ sofaArea K ω
  /-- (I2) Thm 1.5.2 -/
  rotation : ∀ (K : Set ℝ²) (ω : ℝ), IsBalancedMaxCap K ω → arccos (5 / 11) ≤ ω → ω < π / 2 →
    2.2 ≤ sofaArea K ω → ∃ T, IsMonotoneSofa T (π / 2) ∧ ENNReal.ofReal (sofaArea K ω) ≤ volume T
  /-- (I3) Chapters 5–8 -/
  gerver : ∀ K : Set ℝ², IsBalancedMaxCap K (π / 2) →
    ENNReal.ofReal (sofaArea K (π / 2)) ≤ volume G

/-- Every monotone sofa is dominated by any maximizer of `A_ω`. -/
lemma IsMonotoneSofa.volume_le_of_isMax {T : Set ℝ²} (hT : IsMonotoneSofa T ω) (hω0 : 0 < ω)
    (hω1 : ω ≤ π / 2) (hmax : ∀ K' : Set ℝ², IsCap K' ω → sofaArea K' ω ≤ sofaArea K ω) :
    volume T ≤ ENNReal.ofReal (sofaArea K ω) := by
  rw [← ENNReal.ofReal_toReal (hT.volume_ne_top hω0 hω1), ← hT.sofaArea_Ccap hω0 hω1]
  exact ENNReal.ofReal_le_ofReal (hmax _ (hT.isCap_Ccap hω0 hω1))

lemma arccos_five_div_eleven_pos : 0 < arccos (5 / 11) := arccos_pos.2 (by norm_num)

/-- The reduction of Thms 1.5.1 / 1.5.2 with the target `A(K)` of a balanced maximum cap `K` of
rotation angle `π/2`: every moving sofa of area `≥ 2.2` has area `≤ A(K)`. -/
theorem volume_le_sofaArea_of_bmc {s : Set ℝ²} {m : I → E(2)} (hm : IsMovingSofa s m)
    (hvol : ENNReal.ofReal 2.2 ≤ volume s) (hK : IsBalancedMaxCap K (π / 2)) :
    volume s ≤ ENNReal.ofReal (sofaArea K (π / 2)) := by
  obtain ⟨m', θ', hm', hθc, hθ0, hθ, hω1, hω2⟩ := exists_rotationAngle_mem_of_volume_ge hm hvol
  obtain ⟨ω, hω⟩ : ∃ ω, ω = -θ' 1 := ⟨_, rfl⟩
  rw [← hω] at hω1 hω2
  have hω0 : 0 < ω := arccos_five_div_eleven_pos.trans_le hω1
  have hS : IsSofaWithAngle s ω :=
    ⟨0, m', θ', by rwa [tr_zero], hθc, hθ0, hθ, by rw [hω, neg_neg]⟩
  have hstd := stdPos_tr_stdVec hS.isCompact hS.nonempty hω0 hω2
  have hS' := hS.tr' (stdVec s ω)
  obtain ⟨-, -, hsub⟩ := hS'.Imono_props hstd hω0 hω2
  have hmono : IsMonotoneSofa (Imono (tr (stdVec s ω) s) ω) ω := ⟨_, hS', hstd, rfl⟩
  obtain ⟨K₀, hK₀⟩ := exists_isBalancedMaxCap hω0 hω2
  have h1 : volume s ≤ ENNReal.ofReal (sofaArea K₀ ω) := by
    calc volume s = volume (tr (stdVec s ω) s) := (volume_tr _ _).symm
      _ ≤ volume (Imono (tr (stdVec s ω) s) ω) := measure_mono hsub
      _ ≤ _ := hmono.volume_le_of_isMax hω0 hω2 (fun K' hK' => hK₀.isMax hω0 hω2 hK')
  have hKmax : ∀ K' : Set ℝ², IsCap K' (π / 2) → sofaArea K' (π / 2) ≤ sofaArea K (π / 2) :=
    fun K' hK' => hK.isMax (by positivity) le_rfl hK'
  rcases hω2.lt_or_eq with hlt | heq
  · have harea : 2.2 ≤ sofaArea K₀ ω := by
      by_contra hcon
      push Not at hcon
      have := (ENNReal.ofReal_lt_ofReal_iff' (p := sofaArea K₀ ω) (q := 2.2)).2
        ⟨hcon, by norm_num⟩
      exact absurd (hvol.trans h1) (not_le.2 this)
    obtain ⟨T', hT', hvT'⟩ := hK₀.exists_monotoneSofa_pi_div_two hω1 hlt harea
    calc volume s ≤ ENNReal.ofReal (sofaArea K₀ ω) := h1
      _ ≤ volume T' := hvT'
      _ ≤ ENNReal.ofReal (sofaArea K (π / 2)) :=
        hT'.volume_le_of_isMax (by positivity) le_rfl hKmax
  · subst heq
    exact h1.trans (ENNReal.ofReal_le_ofReal (hKmax K₀ hK₀.1))

/-- A balanced maximum cap of rotation angle `π/2` has `A(K) ≥ 2.2` (Hammersley's sofa). -/
theorem IsBalancedMaxCap.two_point_two_le_sofaArea (hK : IsBalancedMaxCap K (π / 2)) :
    11 / 5 ≤ sofaArea K (π / 2) := by
  have hH : ENNReal.ofReal 2.2 ≤ volume hammersleySofa :=
    (ENNReal.ofReal_le_ofReal two_point_two_lt_pi_div_two_add_two_div_pi.le).trans
      volume_hammersleySofa_ge
  have h := hH.trans (volume_le_sofaArea_of_bmc isMovingSofa_hammersleySofa hH hK)
  rcases (ENNReal.ofReal_le_ofReal_iff' (p := 2.2) (q := sofaArea K (π / 2))).1 h with h | h
  · norm_num at h ⊢; linarith
  · norm_num at h

/-- **(I3)** Baek Chapters 5–8: the area functional of a balanced maximum cap with rotation angle
`π/2` is at most the area of Gerver's sofa — from Thm 6.1.1, Thm 8.1.8, Thm 8.2.4 (proved) and
(I3′) `gerver_Qfun_le` (Cor 8.5.8 + Thm 8.4.6), itself derived from (I3″) `gerver_data`. -/
theorem IsBalancedMaxCap.sofaArea_le_gerver (hK : IsBalancedMaxCap K (π / 2)) :
    ENNReal.ofReal (sofaArea K (π / 2)) ≤ volume gerversSofa := by
  obtain ⟨hφ0, hφ1, hQ⟩ := gerver_Qfun_le
  have hA := hK.two_point_two_le_sofaArea
  exact (ENNReal.ofReal_le_ofReal (hK.sofaArea_le_Qfun hA hφ0 hφ1)).trans
    (hQ _ _ _ (hK.inL hA hφ0 hφ1))

namespace Interfaces

variable {G : Set ℝ²} (hI : Interfaces G)
include hI

/-- **The main reduction.** Every moving sofa of area `≥ 2.2` has area at most `|G|`. -/
theorem volume_le_gerver {s : Set ℝ²} {m : I → E(2)}
    (hm : IsMovingSofa s m) (hvol : ENNReal.ofReal 2.2 ≤ volume s) :
    volume s ≤ volume G := by
  obtain ⟨m', θ', hm', hθc, hθ0, hθ, hω1, hω2⟩ := exists_rotationAngle_mem_of_volume_ge hm hvol
  obtain ⟨ω, hω⟩ : ∃ ω, ω = -θ' 1 := ⟨_, rfl⟩
  rw [← hω] at hω1 hω2
  have hω0 : 0 < ω := arccos_five_div_eleven_pos.trans_le hω1
  have hS : IsSofaWithAngle s ω :=
    ⟨0, m', θ', by rwa [tr_zero], hθc, hθ0, hθ, by rw [hω, neg_neg]⟩
  have hstd := stdPos_tr_stdVec hS.isCompact hS.nonempty hω0 hω2
  have hS' := hS.tr' (stdVec s ω)
  obtain ⟨-, -, hsub⟩ := hS'.Imono_props hstd hω0 hω2
  have hmono : IsMonotoneSofa (Imono (tr (stdVec s ω) s) ω) ω := ⟨_, hS', hstd, rfl⟩
  obtain ⟨K, hK⟩ := hI.exists_bmc ω hω0 hω2
  have h1 : volume s ≤ ENNReal.ofReal (sofaArea K ω) := by
    calc volume s = volume (tr (stdVec s ω) s) := (volume_tr _ _).symm
      _ ≤ volume (Imono (tr (stdVec s ω) s) ω) := measure_mono hsub
      _ ≤ _ := hmono.volume_le_of_isMax hω0 hω2 (hI.isMax K ω hK hω0 hω2)
  rcases hω2.lt_or_eq with hlt | heq
  · have harea : 2.2 ≤ sofaArea K ω := by
      by_contra hcon
      push Not at hcon
      have := (ENNReal.ofReal_lt_ofReal_iff' (p := sofaArea K ω) (q := 2.2)).2
        ⟨hcon, by norm_num⟩
      exact absurd (hvol.trans h1) (not_le.2 this)
    obtain ⟨T', hT', hvT'⟩ := hI.rotation K ω hK hω1 hlt harea
    obtain ⟨K', hK'⟩ := hI.exists_bmc (π / 2) (by positivity) le_rfl
    calc volume s ≤ ENNReal.ofReal (sofaArea K ω) := h1
      _ ≤ volume T' := hvT'
      _ ≤ ENNReal.ofReal (sofaArea K' (π / 2)) :=
        hT'.volume_le_of_isMax (by positivity) le_rfl (hI.isMax K' _ hK' (by positivity) le_rfl)
      _ ≤ volume G := hI.gerver K' hK'
  · subst heq
    exact h1.trans (hI.gerver K hK)

/-- **Baek's Theorem 1.1.1 (upper bound)**, conditional on the interface. -/
theorem sofaConstant_le : sofaConstant ≤ volume G := by
  have hH : ENNReal.ofReal 2.2 ≤ volume hammersleySofa :=
    (ENNReal.ofReal_le_ofReal two_point_two_lt_pi_div_two_add_two_div_pi.le).trans
      volume_hammersleySofa_ge
  have hG : ENNReal.ofReal 2.2 ≤ volume G :=
    hH.trans (hI.volume_le_gerver isMovingSofa_hammersleySofa hH)
  refine iSup₂_le fun s hs => ?_
  obtain ⟨m, hm⟩ := hs
  rcases le_or_gt (ENNReal.ofReal 2.2) (volume s) with h | h
  · exact hI.volume_le_gerver hm h
  · exact h.le.trans hG

end Interfaces

/-- The interface, from the chapter-level theorems (all proved). -/
theorem interfaces : Interfaces gerversSofa where
  exists_bmc _ hω0 hω1 := exists_isBalancedMaxCap hω0 hω1
  isMax _ _ hK hω0 hω1 _ hK' := hK.isMax hω0 hω1 hK'
  rotation _ _ hK hω hω1 harea := hK.exists_monotoneSofa_pi_div_two hω hω1 harea
  gerver _ hK := hK.sofaArea_le_gerver

/-- **Baek's Theorem 1.1.1 (upper bound)**: `sofaConstant ≤ |G|`. -/
theorem sofaConstant_le_volume_gerversSofa : sofaConstant ≤ volume gerversSofa :=
  interfaces.sofaConstant_le

/-- **Baek's Theorem 1.1.1**: `sofaConstant = |G|`, Gerver's sofa has the maximal area.  The lower
bound uses that Gerver's sofa is a moving sofa (`Sofa.GP.isMovingSofa_gerversSofa'`, proved from the
upstream definition; the upstream statement `isMovingSofa_gerversSofa` keeps its `sorry`). -/
theorem sofaConstant_eq_volume_gerversSofa' : sofaConstant = volume gerversSofa := by
  refine le_antisymm sofaConstant_le_volume_gerversSofa ?_
  exact le_iSup₂ (f := fun (s : Set ℝ²) (_ : ∃ m, IsMovingSofa s m) => volume s)
    gerversSofa Sofa.GP.isMovingSofa_gerversSofa'

end Sofa
