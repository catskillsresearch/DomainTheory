/-ai
Every domain D is a retract of the function space from D to D.

Specialize the retract that embeds an element as a constant function and retracts by evaluation at bottom.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820.trianglelefteq_funSpace_const

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u v






variable {α : Type u} (D : NeighborhoodSystem α)

/-- **Exercise 8.20, `D ⊴ D→D`.** -/
theorem D_trianglelefteq_funSpace : D ⊴ funSpace D D := trianglelefteq_funSpace_const D D

end DomainTheory.NeighbourhoodSystems
