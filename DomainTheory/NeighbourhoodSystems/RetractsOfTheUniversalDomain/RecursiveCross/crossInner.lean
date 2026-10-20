/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.crossInnerStep

@[expose] public section

set_option linter.unusedSectionVars false

namespace Domain.Recursive

/-- `crossInner bop x c2` codes `[bop (x, y) ∣ y ∈ decodeList c2]` (up to order). -/
def crossInner (bop : ℕ → ℕ) (x c2 : ℕ) : ℕ := foldCode (crossInnerStep bop) x 0 c2

end Domain.Recursive
