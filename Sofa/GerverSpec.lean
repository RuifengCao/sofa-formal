/-
# Sofa/GerverSpec.lean — the upstream Gerver constants

The upstream constants `MovingSofa.GerversSofa.A, B, φ, θ` are defined as the solution of
`ABφθSpec`, through `ABφθSpec.existsUnique`, which is now proved (`Sofa.GC.spec_existsUnique`,
`Sofa/GerverUnique.lean`).  Here: they solve `Sofa.GC.Spec` (`gerver_spec`), `(φ, θ)` lies in the
tight box `|φ − φ₀|, |θ − θ₀| ≤ 2⁻³⁰` (`gerver_mem_tbox`), and Gerver's angle bounds hold
(`gerver_angles`).  All axiom-clean.

STATUS: [PROOF-C-local] round 37 (2026-09-23, Opus 5.5).
-/
import SofaSubmission.Defs

open Real

namespace Sofa.GC

open IA

/-- The upstream constants solve Romik's system. -/
theorem gerver_spec : Spec MovingSofa.GerversSofa.A MovingSofa.GerversSofa.B
    MovingSofa.GerversSofa.φ MovingSofa.GerversSofa.θ :=
  MovingSofa.GerversSofa.ABφθSpec.existsUnique.choose_spec.1

/-- The upstream angles `φ ≈ 0.0391773648`, `θ ≈ 0.6813015094`, to within `2⁻³⁰`. -/
theorem gerver_mem_tbox :
    tbox.1.Mem MovingSofa.GerversSofa.φ ∧ tbox.2.Mem MovingSofa.GerversSofa.θ :=
  Spec_mem_tbox gerver_spec

/-- **Gerver's angles**: `0 < φ ≤ 1/25` and `φ < θ < π/4` for the upstream constants. -/
theorem gerver_angles : 0 < MovingSofa.GerversSofa.φ ∧ MovingSofa.GerversSofa.φ ≤ 1 / 25 ∧
    MovingSofa.GerversSofa.φ < MovingSofa.GerversSofa.θ ∧ MovingSofa.GerversSofa.θ < π / 4 :=
  Spec_angles gerver_spec

end Sofa.GC
