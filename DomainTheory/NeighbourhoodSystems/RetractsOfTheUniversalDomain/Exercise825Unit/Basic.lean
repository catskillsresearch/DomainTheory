module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Unit.isoOfUnique

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}


/-- **There is only one approximable self-map of `𝟙`, the identity.** Both maps induce the same
(unique) elementwise function, so `ext_of_toElementMap` identifies them. -/
instance uniqueApproximableMapUnitSys : Unique (ApproximableMap unitSys unitSys) where
  default := idMap unitSys
  uniq _f := ApproximableMap.ext_of_toElementMap fun _x => Subsingleton.elim _ _

/-- **`(𝟙 → 𝟙)` has a unique element**, transported from the unique approximable self-map of `𝟙`
along `funSpaceEquiv`. -/
instance uniqueFunSpaceUnitSys : Unique (funSpace unitSys unitSys).Element where
  default := (funSpaceEquiv unitSys unitSys).symm default
  uniq _x := (funSpaceEquiv unitSys unitSys).injective (Subsingleton.elim _ _)
end DomainTheory.NeighbourhoodSystems
