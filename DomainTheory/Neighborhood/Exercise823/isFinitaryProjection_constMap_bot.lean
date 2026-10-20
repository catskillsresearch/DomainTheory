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
public import DomainTheory.Neighborhood.Exercise823.isProjection_constMap_bot

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}





theorem isFinitaryProjection_constMap_bot (E : NeighborhoodSystem α) :
    IsFinitaryProjection (constMap E E.bot) :=
  ⟨isProjection_constMap_bot E, Unit, unitSys, ⟨finitaryWitnessEquivBot E⟩⟩

end Exercise823
end DomainTheory.Neighborhood
