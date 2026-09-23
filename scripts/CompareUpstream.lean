/-
# scripts/CompareUpstream.lean — a light-weight self-check of `SofaSubmission`

`comparator` (see `UPSTREAM.md`) is the real check.  This script repeats its comparison of
statements without exporting and replaying the environment (Lean's kernel already checked every
proof when `lake build` compiled it).  It loads the compiled `SofaSubmission/Challenge.olean` as raw
module data next to the environment of `SofaSubmission.Solution`, and checks:

1. `Challenge` imports only `Mathlib` (and the prelude `Init`);
2. each theorem listed in `comparator.json` has literally the same type in both;
3. every constant declared in `Challenge` that these statements use — transitively, through types
   and definition bodies (theorem bodies do not matter) — is declared in `Solution`'s environment
   with the same kind, universe parameters, type and body;
4. the proofs in `Solution` use only the axioms `propext`, `Quot.sound`, `Classical.choice`.

Run after `lake build`: `lake env lean scripts/CompareUpstream.lean`.
-/
import SofaSubmission.Solution

open Lean

def targets : List Name :=
  [`MovingSofa.GerversSofa.ABφθSpec.existsUnique, `MovingSofa.isMovingSofa_gerversSofa,
   `MovingSofa.sofaConstant_eq, `MovingSofa.sofaConstant_eq_volume_gerversSofa]

def permitted : List Name := [``propext, ``Quot.sound, ``Classical.choice]

/-- Constants a declaration contributes to a statement: theorem bodies are irrelevant. -/
def usedInStatement : ConstantInfo → Array Name
  | .thmInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors.toArray
  | .ctorInfo v => v.type.getUsedConstants.push v.induct
  | ci => ci.type.getUsedConstants

def sameInfo : ConstantInfo → ConstantInfo → Bool
  | .defnInfo a, .defnInfo b => a.levelParams == b.levelParams && a.type == b.type && a.value == b.value
  | .opaqueInfo a, .opaqueInfo b => a.levelParams == b.levelParams && a.type == b.type && a.value == b.value
  | .thmInfo a, .thmInfo b => a.levelParams == b.levelParams && a.type == b.type
  | .axiomInfo a, .axiomInfo b => a.levelParams == b.levelParams && a.type == b.type
  | .inductInfo a, .inductInfo b => a.levelParams == b.levelParams && a.type == b.type &&
      a.numParams == b.numParams && a.numIndices == b.numIndices && a.ctors == b.ctors &&
      a.isRec == b.isRec
  | .ctorInfo a, .ctorInfo b => a.levelParams == b.levelParams && a.type == b.type &&
      a.induct == b.induct && a.cidx == b.cidx && a.numParams == b.numParams &&
      a.numFields == b.numFields
  | .recInfo a, .recInfo b => a.levelParams == b.levelParams && a.type == b.type
  | .quotInfo a, .quotInfo b => a.levelParams == b.levelParams && a.type == b.type
  | _, _ => false

run_cmd do
  let env ← getEnv
  let (mod, _) ← readModuleData ".lake/build/lib/lean/SofaSubmission/Challenge.olean"
  let mut ok := true
  -- 1. imports
  let imps := mod.imports.map (·.module)
  if imps.all (fun m => m == `Mathlib || m == `Init) then
    logInfo m!"Challenge imports: {imps}"
  else
    logError m!"Challenge imports more than Mathlib: {imps}"; ok := false
  let mut chal : Std.HashMap Name ConstantInfo := {}
  for ci in mod.constants do
    chal := chal.insert ci.name ci
  -- 2. statements
  let mut stack : List Name := []
  for t in targets do
    match chal.get? t, env.find? t with
    | some a, some b =>
      if a.type == b.type then
        logInfo m!"same statement: {t}"
      else
        logError m!"DIFFERENT statement: {t}"; ok := false
      stack := a.type.getUsedConstants.toList ++ stack
    | _, _ =>
      logError m!"missing in Challenge or Solution: {t}"; ok := false
  -- 3. the Challenge declarations behind the statements
  let mut seen : NameSet := {}
  let mut compared : Array Name := #[]
  while !stack.isEmpty do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if seen.contains c then continue
      seen := seen.insert c
      if let some a := chal.get? c then
        compared := compared.push c
        match env.find? c with
        | some b =>
          unless sameInfo a b do
            logError m!"DIFFERENT declaration: {c}"; ok := false
        | none =>
          logError m!"missing in Solution: {c}"; ok := false
        stack := (usedInStatement a).toList ++ stack
  logInfo m!"compared {compared.size} Challenge declarations used by the statements: {compared.qsort Name.lt}"
  -- 4. axioms of the Solution proofs
  for t in targets do
    let axs ← collectAxioms t
    if axs.all (permitted.contains ·) then
      logInfo m!"{t} uses axioms {axs}"
    else
      logError m!"{t} uses NON-PERMITTED axioms {axs}"; ok := false
  if ok then logInfo "RESULT: OK" else logError "RESULT: FAILED"
