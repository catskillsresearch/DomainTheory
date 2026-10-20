/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.myAndNot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.myAndNot_eq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.levelSet_diff_same_level

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **Computable version of `levelSet_diff_same_level`, upsampled to a common level** — mirrors
`levelSet_myInter` exactly, substituting `myAndNot` for `myLand`. -/
theorem levelSet_myDiff (k1 m1 k2 m2 : ℕ) :
    levelSet k1 m1 \ levelSet k2 m2
      = levelSet (max k1 k2) (myAndNot (myUpsample k1 (max k1 k2) m1) (myUpsample k2 (max k1 k2) m2)) := by
  conv_lhs => rw [← levelSet_myUpsample (Nat.le_max_left k1 k2) (m := m1),
    ← levelSet_myUpsample (Nat.le_max_right k1 k2) (m := m2)]
  rw [levelSet_diff_same_level, myAndNot_eq]

end DomainTheory.NeighbourhoodSystems
