/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Example78

open Domain.Recursive NeighborhoodSystem

/-- The neighbourhood `ℕ ∖ Eₙ` of the powerset domain: the cofinite set of bit positions **not**
set in `n`. Scott's `Eₙ` is `{k ∣ n.testBit k}`, so `nbhd n = {k ∣ n.testBit k = false}`. -/
def nbhd (n : ℕ) : Set ℕ := {k | n.testBit k = false}

end DomainTheory.NeighbourhoodSystems.Example78
