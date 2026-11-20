/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
import Lake

/-!
# Package configuration

This file configures the library for Theorem 1.1 and the index of numbered results.
-/

open Lake DSL

package abcTwoNinths where
  moreLeanArgs := if (get_config? strict).isSome then #["-DwarningAsError=true"] else #[]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "25e572b8074098af3f09d4cb2a4231cbdc584534"

@[default_target]
lean_lib AbcTwoNinths where
  roots := #[`AbcTwoNinths, `Challenge, `Solution, `PaperMap]
  globs := #[.submodules `AbcTwoNinths, .one `AbcTwoNinths, .one `Challenge, .one `Solution, .one `PaperMap]
