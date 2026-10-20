/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.crossOuterStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace Domain.Recursive

/-- **`crossCombine bop c1 c2`** codes `[bop (x, y) ∣ x ∈ decodeList c1, y ∈ decodeList c2]`
(up to order/duplicates), i.e. the code-level analogue of `L1.flatMap (fun x => L2.map (bop x ·))`.
This is the workhorse behind `Definition87.lean`'s `combineIntervals` at the code level. -/
def crossCombine (bop : ℕ → ℕ) (c1 c2 : ℕ) : ℕ := foldCode (crossOuterStep bop) c2 0 c1

end Domain.Recursive
