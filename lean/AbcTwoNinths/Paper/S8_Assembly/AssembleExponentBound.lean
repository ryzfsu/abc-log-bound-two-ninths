/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/

module

public import AbcTwoNinths.Paper.S8_Assembly.PolynomialBoundTail
public import AbcTwoNinths.Paper.S8_Assembly.CommonTail

/-!
# Assemble Exponent Bound

The polynomial height cap, the fixed-margin exterior estimates, and band exclusion give the
bound with exponent `2/9 + ε`. This is Lemma 8.2 of the paper.

## Main results
* `AbcTwoNinths.Assembly.logBoundOfProviders`
-/

@[expose] public section

namespace AbcTwoNinths.Assembly

section

/-- Lemma 8.2 of the paper. This is used in Section 8 of the paper. -/
theorem logBoundOfProviders (cap : _root_.AbcTwoNinths.Statement.PolyCap)
    (exterior : _root_.AbcTwoNinths.Statement.FixedMarginExterior) (engine : _root_.AbcTwoNinths.Terminal.BandEngine) :
    twoNinthsStatement :=
  _root_.AbcTwoNinths.Assembly.twoNinthsOfPolycapAndTail cap (_root_.AbcTwoNinths.Assembly.commonTailOf exterior engine)

end

end AbcTwoNinths.Assembly
