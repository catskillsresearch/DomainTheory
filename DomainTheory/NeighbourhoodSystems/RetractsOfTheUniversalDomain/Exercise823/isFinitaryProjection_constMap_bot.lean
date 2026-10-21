/-ai
The constant-bottom map is a finitary projection.

It is a projection, and the unit type with the terminal neighbourhood system witnesses finitariness through the order isomorphism of its fixed-point set with the terminal system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise816
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.isProjection_constMap_bot

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}





theorem isFinitaryProjection_constMap_bot (E : NeighborhoodSystem α) :
    IsFinitaryProjection (constMap E E.bot) :=
  ⟨isProjection_constMap_bot E, Unit, unitSys, ⟨finitaryWitnessEquivBot E⟩⟩

end Exercise823
end DomainTheory.NeighbourhoodSystems
