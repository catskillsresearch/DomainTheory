/-ai
Every domain D is a retract of the product of D with itself.

Specialize the retract that embeds an element as a pair with bottom in the second component and retracts by the first projection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.trianglelefteq_prod_fst

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u


variable {α : Type u} (D : NeighborhoodSystem α)

/-- **Exercise 8.20, `D ⊴ D×D`.** -/
theorem D_trianglelefteq_prod : D ⊴ prod D D := trianglelefteq_prod_fst D D

end DomainTheory.NeighbourhoodSystems
