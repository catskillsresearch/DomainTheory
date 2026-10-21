/-ai
The function space of the one-point domain with itself is isomorphic to the one-point domain. The terminal domain is a fixed point of the function-space construction, which is why the obvious solution by retracts carries no information.

The proof applies the isomorphism of neighbourhood systems whose element posets are unique.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Unit.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Unit.isomorphic_of_unique

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*}


/-- **Exercise 8.25 (Scott 1981, PRG-19) — the obstruction `𝟙 → 𝟙 = 𝟙`.** The terminal one-point
domain is a fixed point of `→`, carrying no information: this is why "the obvious solution by
retracts is of no use". -/
theorem funSpace_unitSys_isomorphic : funSpace unitSys unitSys ≅ᴰ unitSys :=
  isomorphic_of_unique _ _

end DomainTheory.NeighbourhoodSystems
