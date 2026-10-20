/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel.minLevel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- **`minMask k m`**: `m`'s own bits, truncated to `minLevel k m`'s width — the presentation-
independent canonical mask of the set `levelSet k m` (`minLevel_unique`). -/
def minMask (k m : ℕ) : ℕ := myModPow2 m (2 ^ minLevel k m)

end DomainTheory.NeighbourhoodSystems
