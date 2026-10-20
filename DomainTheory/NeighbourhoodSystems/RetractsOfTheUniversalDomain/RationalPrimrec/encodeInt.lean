/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- Encode an integer as the difference-pair `(z.toNat, (-z).toNat)` (one of the two is always
`0`). -/
def encodeInt (z : ℤ) : ℕ := Nat.pair z.toNat (-z).toNat

end DomainTheory.NeighbourhoodSystems
