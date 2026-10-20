/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.consStep2

@[expose] public section

set_option linter.unusedSectionVars false

namespace Domain.Recursive

/-- `appendCode c1 c2` codes a list with the same **elements** as `decodeList c1 ++ decodeList c2`
(reversed on the `c1` side, since `foldCode` conses left-to-right; irrelevant for set-level uses). -/
def appendCode (c1 c2 : ℕ) : ℕ := foldCode consStep2 0 c2 c1

end Domain.Recursive
