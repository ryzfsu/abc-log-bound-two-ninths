/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import AbcTwoNinths.Statement
public import AbcTwoNinths.Paper.S8_Assembly.MainTheorem

/-!
# Proof of the upper bound for log c

The assembly theorem gives the bound of Theorem 1.1 for positive coprime triples.

## Main results
* `AbcTwoNinths.twoNinths`
-/

@[expose] public section

namespace AbcTwoNinths

/-- Theorem 1.1 of the paper. -/
theorem twoNinths : twoNinthsStatement := AbcTwoNinths.Assembly.logBound

end AbcTwoNinths
