/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Uunion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.decodeQPairList_appendListCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`Uunion` realizes set union at the raw (uncanonicalized) `presentedIntervals` level**,
unconditionally — concatenating presenting lists always presents the union, no consistency case
split needed (the one respect in which `∪` is even simpler than `\`'s `Udiff_eq_diff`). -/
theorem Uunion_eq_union (n m : ℕ) :
    presentedIntervals (decodeQPairList (Uunion n m)) = UX n ∪ UX m := by
  unfold Uunion
  rw [decodeQPairList_appendListCode, presentedIntervals_append]
  rfl

end DomainTheory.NeighbourhoodSystems
