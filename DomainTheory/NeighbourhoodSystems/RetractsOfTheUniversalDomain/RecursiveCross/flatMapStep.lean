/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.appendCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace Domain.Recursive

/-- `foldCode`'s step for `flatMapCode`: pops `y` from the folded list, appends `f (pair x y)`
(`x` threaded as the fixed parameter) onto the accumulator. -/
def flatMapStep (f : ℕ → ℕ) (w : ℕ) : ℕ :=
  appendCode (f (Nat.pair w.unpair.2.unpair.2 w.unpair.1)) w.unpair.2.unpair.1

end Domain.Recursive
