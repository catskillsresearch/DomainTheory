module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise816
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.finitaryWitnessEquivBot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.tOp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.fixOp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.eq_bot_of_fixed_constMap_bot
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823.uniqueFixedConstMapBot

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Sub8_6

namespace Exercise823

variable {α : Type} {E : NeighborhoodSystem α}


/-- The fixed-point-set ("`D_a`") of an approximable self-map, matching `IsFinitary`'s own
formulation. -/
abbrev Fix (a : ApproximableMap E E) := {y : E.Element // a.toElementMap y = y}
end Exercise823
end DomainTheory.NeighbourhoodSystems
