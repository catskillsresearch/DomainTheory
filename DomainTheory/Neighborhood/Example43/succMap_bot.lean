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
public import DomainTheory.Neighborhood.Example43.constLiftN_bot

@[expose] public section


namespace DomainTheory.Neighborhood.Example43

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap



















/-- `succ(⊥) = ⊥`. -/
theorem succMap_bot : succMap.toElementMap N.bot = N.bot :=
  constLiftN_bot N (fun n => natElem (n + 1))

end DomainTheory.Neighborhood.Example43
