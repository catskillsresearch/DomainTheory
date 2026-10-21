/-ai
The infinite iterate of a domain is isomorphic to the product of that domain with the iterate.

The isomorphism is the order isomorphism between the iterate and that product.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}









variable (V : NeighborhoodSystem α)


variable {V}





























/-- **Exercise 3.16 (Scott 1981, PRG-19).** `𝒟^∞ ≅ 𝒟 × 𝒟^∞`. -/
theorem iter_isomorphic (V : NeighborhoodSystem α) : iterSys V ≅ᴰ prod V (iterSys V) :=
  ⟨iterProdIso V⟩

end DomainTheory.NeighbourhoodSystems
