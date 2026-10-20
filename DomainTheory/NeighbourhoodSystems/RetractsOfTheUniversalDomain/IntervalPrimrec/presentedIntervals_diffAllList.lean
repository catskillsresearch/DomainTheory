/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RationalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec.presentedIntervals_foldl_diffSingleList

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive



















theorem presentedIntervals_diffAllList (p : ℚ × ℚ) (L2 : List (ℚ × ℚ)) :
    presentedIntervals (diffAllList p L2) = Set.Ico p.1 p.2 \ presentedIntervals L2 := by
  unfold diffAllList
  rw [presentedIntervals_foldl_diffSingleList, presentedIntervals_cons, presentedIntervals_nil,
    Set.union_empty]

end DomainTheory.NeighbourhoodSystems
