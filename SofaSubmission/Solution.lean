/-
# SofaSubmission/Solution.lean — proofs of the upstream statements

The four statements of `SofaSubmission/Challenge.lean` (= formal-conjectures'
`FormalConjectures/Wikipedia/MovingSofa.lean`) that this project proves, restated with their
proofs.  `ABφθSpec.existsUnique` is already proved where it is declared (`SofaSubmission/Defs.lean`),
because the constants `A, B, φ, θ` are defined from it.  The open statement
`volume_eq_sofaConstant_iff_congruent_gerversSofa` (uniqueness of the optimal sofa) is not here.

Check with `comparator` (see `UPSTREAM.md`):
`lake env <comparator> comparator.json` verifies that each theorem listed in `comparator.json`
has the same statement here as in `Challenge.lean` (with the same definitions), uses only
`propext`, `Quot.sound`, `Classical.choice`, and is accepted by the Lean kernel.
-/
import Sofa.Main

namespace MovingSofa

/-- Gerver's concrete sofa admits a valid hallway motion. -/
theorem isMovingSofa_gerversSofa : ∃ m, IsMovingSofa gerversSofa m :=
  Sofa.GP.isMovingSofa_gerversSofa'

open MeasureTheory

/-- What is the sofa constant? -/
theorem sofaConstant_eq : sofaConstant = volume gerversSofa :=
  Sofa.sofaConstant_eq_volume_gerversSofa'

/-- Gerver's sofa attains the sofa constant, conjectured by [Ge92] and claimed by [Ba24]. -/
theorem sofaConstant_eq_volume_gerversSofa : sofaConstant = volume gerversSofa :=
  Sofa.sofaConstant_eq_volume_gerversSofa'

end MovingSofa
