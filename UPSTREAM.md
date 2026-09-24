# Submitting to formal-conjectures

This repository proves four statements of
[`FormalConjectures/Wikipedia/MovingSofa.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Wikipedia/MovingSofa.lean)
in google-deepmind/formal-conjectures. formal-conjectures is a *statement* repository: proofs longer
than 25–50 lines stay in their own repository and are linked from the statement with
`@[formal_proof using lean4 at "<url>"]` (their `CONTRIBUTING.md`). A declaration may carry several
`formal_proof` tags.

## What is proved

| Upstream declaration | Upstream status (2026-09-23) | Here |
|---|---|---|
| `GerversSofa.ABφθSpec.existsUnique` | `textbook`, `sorry`, **no** `formal_proof` | proved (`Sofa/GerverUnique.lean`, via interval arithmetic) |
| `isMovingSofa_gerversSofa` | `research solved`, linked to Trela's GerverSofaLean | proved (`Sofa/GerverConn.lean`) |
| `sofaConstant_eq` | `research solved`, linked to Cureton's MovingSofa | proved (Baek's theorem, `Sofa/Main.lean`) |
| `sofaConstant_eq_volume_gerversSofa` | `research solved`, linked to Cureton's MovingSofa | proved (same) |
| `volume_eq_sofaConstant_iff_congruent_gerversSofa` | `research open` | **not proved** (uniqueness is open) |

All four proofs use only `propext`, `Classical.choice`, `Quot.sound`.

## Layout

* `SofaSubmission/Defs.lean`: the upstream definitions — `Challenge.lean` with the four `sorry`ed
  theorems left out and `ABφθSpec.existsUnique` proved in place (because `A, B, φ, θ` are defined
  from it). Every module of the proof imports it. It is one file in the upstream order, in the
  same root namespace as `Challenge.lean`, because Lean names the anonymous `TopologicalSpace E(2)`
  instance after the module's root namespace and shares auxiliary proofs (e.g. of
  `Nat.AtLeastTwo 2`) only within a file; this makes the declarations behind the upstream
  statements literally equal to those of `Challenge.lean`.
* `SofaSubmission/Challenge.lean`: the whole upstream file with its `sorry`s. It imports only
  Mathlib. It differs from the upstream file at commit `0771383` in five syntactic ways, which let
  it build without the formal-conjectures library and leave the definitions and statements
  unchanged: `import Mathlib` instead of `FormalConjecturesUtil`; no module-system header
  (`module`, `public import`, `@[expose] public section`); no `@[category …]`/`formal_proof`
  attributes; `answer(volume gerversSofa)` written `volume gerversSofa`; the `ℝ²` notation and two
  instances copied from `FormalConjecturesForMathlib/Geometry/2d.lean`. (Its header names the
  commit `40e7c98` from which it was first copied; the upstream file changed after that only in
  its module-system header and in two `formal_proof` attributes.)
* `SofaSubmission/Solution.lean`: the same theorems with proofs (it imports `Sofa.Main`).
* `comparator.json`: configuration for [comparator](https://github.com/leanprover/comparator).

## Checking with comparator

comparator builds `Challenge` and `Solution` in a sandbox, checks that every theorem in
`theorem_names` has the same statement in both (with the same definitions behind it), that its
proof uses only the permitted axioms, and replays the proof into the Lean kernel.

```bash
# 1. this repository
lake exe cache get          # Mathlib oleans
lake build                  # Sofa + SofaSubmission

# 2. comparator and lean4export for Lean v4.33 (tag v4.33.0 of both works with v4.33.1)
git clone --branch v4.33.0 https://github.com/leanprover/comparator
cd comparator && lake build lean4export comparator && cd ..
# landrun (Linux sandbox) from https://github.com/Zouuup/landrun, or for a quick local check the
# development stand-in comparator/scripts/fake-landrun.sh (no sandboxing!)

# 3. run it from this repository's root
COMPARATOR_LANDRUN=$(realpath comparator/scripts/fake-landrun.sh) \
COMPARATOR_LEAN4EXPORT=$(realpath comparator/.lake/packages/lean4export/.lake/build/bin/lean4export) \
  lake env comparator/.lake/build/bin/comparator comparator.json
```

With a real `landrun`, follow comparator's README (`systemd-run … lake env comparator …`).

**Result (2026-09-23):** passed. comparator was built at tag v4.33.0 with Lean 4.33.1 and run with
`fake-landrun.sh` (no sandbox) and without nanoda. It printed `Lean default kernel accepts the
solution` and `Your solution is okay!` after 23 minutes on a 2-core, 8 GB machine. Its output is in
`verification/comparator-r42.txt`. The lighter `lake env lean scripts/CompareUpstream.lean` prints
`RESULT: OK` (`verification/compare-upstream-r42.txt`).

**Second run (2026-09-24):** a verification of commit `838baca` ran comparator v4.33.0 against a
challenge generated mechanically from the upstream file at commit `0771383` (apart from comments,
identical to `Challenge.lean`), with nanoda 0.4.19 enabled. It printed `Nanoda kernel accepts the
solution`, `Lean default kernel accepts the solution` and `Your solution is okay!`. The report is
posted on TheJustinSunPrize/awards#4441.

## Upstream submission

Issue google-deepmind/formal-conjectures#6525 and PR #6526 (open on 2026-09-24). The PR changes
attributes only: it adds `formal_proof using lean4` links to this repository, as permalinks to
commit `838baca` with line numbers, and keeps every upstream proof `sorry`.

| Upstream declaration | Link target |
|---|---|
| `GerversSofa.ABφθSpec.existsUnique` | `SofaSubmission/Defs.lean#L173` (first link) |
| `isMovingSofa_gerversSofa` | `SofaSubmission/Solution.lean#L20` (second link) |
| `sofaConstant_eq` | `SofaSubmission/Solution.lean#L26` (second link) |
| `sofaConstant_eq_volume_gerversSofa` | `SofaSubmission/Solution.lean#L30` (second link) |

At the reviewer's request the PR also pins the two existing links of `sofaConstant_eq` and
`sofaConstant_eq_volume_gerversSofa` to a commit in the same way.

Notes for a check against the upstream file itself (rather than `Challenge.lean`):
`answer(x)` upstream elaborates to `x` wrapped in an `mdata` annotation (`FormalConjecturesUtil/Answer.lean`,
`mkAnnotation `answer`). The kernel ignores `mdata`, but a structural comparison of statements does
not, so such a check has to put the same annotation on `sofaConstant_eq` in the solution. The
`formal_proof` linter requires the upstream proofs to stay `sorry`; this PR keeps them.
