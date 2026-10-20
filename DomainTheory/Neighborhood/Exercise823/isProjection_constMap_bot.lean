/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem86
public import DomainTheory.Neighborhood.Theorem41
public import DomainTheory.Neighborhood.Exercise315
public import DomainTheory.Neighborhood.Exercise816
public import DomainTheory.Neighborhood.Exercise823.Basic
public import DomainTheory.Neighborhood.Exercise823.isRetraction_constMap_bot
public import DomainTheory.Neighborhood.Exercise823.constMap_bot_le_idMap

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}


theorem isProjection_constMap_bot (E : NeighborhoodSystem α) :
    IsProjection (constMap E E.bot) :=
  ⟨isRetraction_constMap_bot E, constMap_bot_le_idMap E⟩

end Exercise823
end DomainTheory.Neighborhood
