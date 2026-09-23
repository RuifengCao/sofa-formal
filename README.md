# sofa-formal — a Lean 4 proof that Gerver's sofa is optimal

A formalization of J. Baek, *Optimality of Gerver's Sofa* (arXiv:2411.19826, 2024), in Lean 4 with
Mathlib, for the definitions of google-deepmind/formal-conjectures
(`FormalConjectures/Wikipedia/MovingSofa.lean`).

## Status (2026-09-23, round 42)

```lean
theorem Sofa.sofaConstant_eq_volume_gerversSofa' : sofaConstant = volume gerversSofa
-- #print axioms: [propext, Classical.choice, Quot.sound]
```

Gerver's sofa attains the maximal area of a moving sofa. No `sorry` is used, and no axioms beyond
Lean's standard three. The build and the axiom audit (`Sofa/Check.lean`) have been reproduced on a
second machine (Windows); the audit output was identical line by line.

Proved statements of the upstream file (see `UPSTREAM.md`). comparator checked them against a
verbatim copy of that file (`comparator.json`) and passed:

| Upstream | Here |
|---|---|
| `GerversSofa.ABφθSpec.existsUnique` (Gerver's constants exist and are unique) | `Sofa/GerverUnique.lean`, used in `SofaSubmission/Defs.lean` |
| `isMovingSofa_gerversSofa` | `Sofa.GP.isMovingSofa_gerversSofa'` (`Sofa/GerverConn.lean`) |
| `sofaConstant_eq`, `sofaConstant_eq_volume_gerversSofa` | `Sofa.sofaConstant_eq_volume_gerversSofa'` (`Sofa/Main.lean`) |
| `volume_eq_sofaConstant_iff_congruent_gerversSofa` (uniqueness) | **open**; Baek does not claim it |

The statements, with their proofs, are collected in `SofaSubmission/Solution.lean`.

## What is formalized

Every step of Baek's proof, and every fact about Gerver's sofa that Baek imports or leaves unproved:

| Baek | Content | Modules |
|---|---|---|
| Ch. 1 | Hammersley's bounds `π/2 + 2/π ≤ sofaConstant ≤ 2√2`, a sofa of area `> 2.2` (used in Thm 1.5.1) | `Hammersley`, `HammersleySofa`, `HammersleyArea` |
| Ch. 2 | support functions, rotation angle and motions, monotone sofas, standard position, `I(S)`, `C(S)`, caps and niches, Thms 2.3.x–2.5.10, Thm 1.5.1 | `Basic`, `Support`, `SupportLipschitz`, `RotationAngle`, `Motion`, `RotationBound`, `Monotone`, `StdPos`, `MonoSofa`, `Cap`, `CapNiche`, `CapThm`, `Vertex`, `Mirror`, `Hausdorff` |
| Ch. 3–5 | polygon caps, the area derivative, balanced maximum caps, Thm 1.5.2 (angle `< π/2`) | `PolyCap`, `Nef`, `Graph`, `PolyGraph`, `PolyBalance`, `PolyMax`, `BalancedMax`, `SideLength`, `RightAngle`, `Width`, `RotateSofa`, `Thm152` |
| Ch. 6 | surface area measure, arm lengths, Thms 6.3.3, 6.4.3, 6.5.1, 6.5.6, **Thm 6.1.1** (balanced maximum caps are injective) | `SurfaceArea`, `SurfaceThm`, `ArmLength`, `Injective`, `NicheBound`, `GapArm`, `ArmLimit`, `GapSum`, `PolyGap`, `MirrorArm`, `EndPoint`, `ArmPairK`, `AbsCont`, `ArmBound`, `SigmaLimit` |
| Ch. 7 | Thm 7.1.3 `\|K\| = ½∫h dσ`, Thm 7.1.5, curve areas, `J(u^{a,b}_K)`, **Mamikon's theorem** (Thm 7.4.1) | `Triangle`, `SectorArea`, `AreaThm`, `VertexOrder`, `WedgeCover`, `Translate`, `Quadratic`, `Minkowski`, `StieltjesIBP`, `CurveArea`, `Mamikon`, `MamikonLine`, `CapHalf`, `TangentCap` |
| Ch. 8 | `𝒬` and its domain `𝓛`, Thm 8.1.8, **Thm 8.2.4** `𝒜(K) ≤ 𝒬`, **Thm 8.3.8** (concavity), Thms 8.4.3–8.4.6, Thms 8.5.1–8.5.7, Cor 8.5.8 | `ConcaveQ`, `NicheSide`, `NicheCore`, `DirDerivQ`, `QMax`, `GerverFaces`, `GerverArea`, `GerverODE` |
| Gerver's sofa | constants (interval arithmetic), moving sofa, `I(G) = G`, Romik's ODEs (Thm 8.4.2), Thm 8.4.1 (1)–(4), Thm 6.1.2 | `IntervalArith`, `GerverConst`, `GerverUnique`, `GerverSpec`, `GerverPath`, `GerverClosed`, `GerverConn`, `GerverMono`, `GerverCap`, `GerverRomik`, `GerverEnds`, `GerverTailDeriv`, `GerverInj`, `GerverArch`, `GerverNiche` |
| Thm 1.1.1 | assembly | `Main` |

Deviations from the paper (details in `blueprint/`): Green's theorem and the
Jordan-curve arguments of Ch. 7–8 are replaced by explicit area computations; the area derivative of
Ch. 3 is proved by slicing instead of cell decompositions; the Portmanteau step of Lemma 6.4.2 is
avoided. Baek does not prove Thm 8.4.1 and imports Thms 6.1.2 and 8.4.2; all three are proved here for
the upstream `gerversSofa`. Not formalized: Green's theorem itself (Thm 7.2.3, Prop 7.2.7,
Lemmas 7.3.1, 7.3.5), which the proof does not need.

## Build

Lean `v4.33.1`, Mathlib `v4.33.1` (the same pins as formal-conjectures).

```bash
lake exe cache get          # Mathlib oleans
lake build                  # 8794 jobs; the only warnings are the `sorry`s of SofaSubmission/Challenge.lean
```

Building the project itself (after the Mathlib cache) took about 40 minutes of CPU time on a
Windows laptop (round 41). Modules that do not depend on each other build in parallel, and the
longest chain of dependent modules is estimated at about 20 minutes. The slowest module is
`GerverConn` (≈ 75 s, mostly kernel-checked interval arithmetic); everything else takes seconds to
tens of seconds beyond loading Mathlib.

## Axiom audit

```bash
lake env lean Sofa/Check.lean > check.txt; echo "exit=$?"; grep -c sorryAx check.txt; tail -6 check.txt
```

Expected: `exit=0`, `0`, and six lines — the main theorem and the four upstream statements — each
ending in `[propext, Classical.choice, Quot.sound]`. Every line of `check.txt` lists a subset of these
three axioms (the interval-arithmetic definitions use fewer or none).

## Layout

* `SofaSubmission/Defs.lean` — the upstream definitions: `Challenge.lean` without its `sorry`ed
  theorems and with `ABφθSpec.existsUnique` proved. Every module of the proof imports it.
* `Sofa/*.lean` — the proof, one module per section or theorem of the paper; `Sofa.lean` imports all.
  Each module imports only the modules whose declarations it uses, so independent chapters build in
  parallel.
* `Sofa/Check.lean` — the axiom audit (every named result).
* `SofaSubmission/Challenge.lean`, `SofaSubmission/Solution.lean`, `comparator.json` — the upstream
  statements and their proofs, for comparator (`UPSTREAM.md`).
* `blueprint/` — the proof blueprint, written from the paper before and during the formalization.
  Its status flags record the plan at the time of writing.
* `verification/` — outputs of the axiom audit, `scripts/CompareUpstream.lean` and comparator.

A few source comments cite `PLAN.md`, the author's development plan, which is not part of this
repository.

License: Apache-2.0 (`LICENSE`); the files copied from formal-conjectures (`SofaSubmission/Defs.lean`,
`SofaSubmission/Challenge.lean`) are Apache-2.0, Copyright The Formal Conjectures Authors.
