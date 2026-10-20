module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.trianglelefteq_prod_fst

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u v






variable {α : Type u} (D : NeighborhoodSystem α)

/-- **Exercise 8.20, `D ⊴ D×D`.** -/
theorem D_trianglelefteq_prod : D ⊴ prod D D := trianglelefteq_prod_fst D D

end DomainTheory.NeighbourhoodSystems
