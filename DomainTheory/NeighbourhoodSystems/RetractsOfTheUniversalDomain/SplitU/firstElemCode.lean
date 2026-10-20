/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- The code of the head element of a non-empty list-code `c` (`decodeList c`'s head). Junk
(`0`'s `unpair.1`) when `c = 0`, but we only ever apply it to `canonCode n ≠ 0`
(`canonCode_ne_zero`). -/
def firstElemCode (c : ℕ) : ℕ := (c - 1).unpair.1

end DomainTheory.NeighbourhoodSystems
