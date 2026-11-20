/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

import Lean

/-!
# Statement identity for Theorem 1.1

This program compares the theorem types in `Challenge` and `Solution`, along
with the definitions of the radical, the triple hypotheses and the bound.

## Main declarations
* `main`
-/

open Lean

private def getDeclaration (env : Environment) (name : Name) : IO ConstantInfo :=
  match env.find? name with
  | some info => pure info
  | none => throw <| IO.userError s!"Missing declaration: {name}"

/-- Compare the two presentations of Theorem 1.1 and emit the identity report. -/
public def main (args : List String) : IO Unit := do
  let modules ← match args with
    | [] => pure (`Challenge, `Solution)
    | [first, second] => pure (first.toName, second.toName)
    | _ => throw <| IO.userError "Expected zero or two module names"
  Lean.initSearchPath (← Lean.findSysroot)
  let left ← Lean.importModules #[{ module := modules.1 }] {}
  let right ← Lean.importModules #[{ module := modules.2 }] {}
  let statement := `AbcTwoNinths.twoNinthsStatement
  let theoremName := `AbcTwoNinths.twoNinths
  let leftTheorem ← getDeclaration left theoremName
  let rightTheorem ← getDeclaration right theoremName
  unless leftTheorem.type == mkConst statement && leftTheorem.type == rightTheorem.type do
    throw <| IO.userError "The theorem types differ or do not name the fixed statement"
  let definitions := #[`AbcTwoNinths.radNat, `AbcTwoNinths.TwoNinthsTriple, statement]
  for name in definitions do
    let l ← getDeclaration left name
    let r ← getDeclaration right name
    let some body := l.value? | throw <| IO.userError s!"Expected a fixed definition: {name}"
    unless l.type == r.type && some body == r.value? do
      throw <| IO.userError s!"Fixed definition differs: {name}"
  IO.println <| (Json.mkObj [
    ("state", toJson "PASS_STATEMENT_AND_FIXED_DEFINITIONS"),
    ("challenge_module", toJson modules.1.toString),
    ("solution_module", toJson modules.2.toString),
    ("main_theorem", toJson theoremName.toString),
    ("challenge_solution_theorem_type_identical", toJson true),
    ("fixed_definition_bodies_identical", toJson (definitions.map Name.toString))]).pretty
