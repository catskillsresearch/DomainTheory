/-ai
The swap from the product of the product of E with itself and the three-point domain into the product of the three-point domain and the product of E with itself exchanges the two factors, so that a conditional whose domain is shaped as the three-point domain times E times E can be fed from a domain shaped as that product times the three-point domain.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u

section Prod

variable {α : Type u} {E : NeighborhoodSystem α}

/-- The "swap" map `(E×E)×T → T×(E×E)`, used to feed `cond`'s `T×E×E`-shaped domain from a
`(E×E)×T`-shaped one so it can be curried away from the `T`-argument. -/
noncomputable def swapProdT : ApproximableMap (prod (prod E E) TD) (prod TD (prod E E)) :=
  paired (proj₁ (prod E E) TD) (proj₀ (prod E E) TD)

end Prod

end DomainTheory.NeighbourhoodSystems
