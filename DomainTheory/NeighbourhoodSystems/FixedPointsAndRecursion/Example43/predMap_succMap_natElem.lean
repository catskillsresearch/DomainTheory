/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Example23
public import DomainTheory.Neighborhood.Theorem41
public import DomainTheory.Neighborhood.Example43.Basic
public import DomainTheory.Neighborhood.Example43.succMap_natElem
public import DomainTheory.Neighborhood.Example43.predMap_natElem_succ

@[expose] public section


namespace DomainTheory.Neighborhood.Example43

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap



























/-- `pred(succ(n̂)) = n̂`: the predecessor undoes the successor on total elements. (A sample of the
"recursion" reasoning Scott highlights; cf. the iterated-summation example.) -/
theorem predMap_succMap_natElem (n : ℕ) :
    predMap.toElementMap (succMap.toElementMap (natElem n)) = natElem n := by
  rw [succMap_natElem, predMap_natElem_succ]

end DomainTheory.Neighborhood.Example43
