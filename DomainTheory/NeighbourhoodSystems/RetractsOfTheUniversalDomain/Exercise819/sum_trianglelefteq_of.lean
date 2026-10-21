/-ai
If the three-point domain is a retract of E and the function space from E to E is a retract of E, then the sum of E with itself is a retract of E.

The product of E with itself is already a retract of E. Chain the retract of the sum into the product of the three-point domain with that product, the left functoriality that replaces the three-point domain by E, the right functoriality that replaces the inner product by E, and the retract of the product into E.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.prod_left_trianglelefteq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.prod_right_trianglelefteq
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.prod_trianglelefteq_of
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise819.sum_trianglelefteq_prodT

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326

universe u








section Sum

variable {α : Type u} {E : NeighborhoodSystem α} (hE : ∀ X, E.mem X → X.Nonempty)


/-- **Exercise 8.19, Goal 2.** `T ⊴ E` and `E → E ⊴ E` give `E + E ⊴ E`: chain
`E+E ⊴ T×(E×E) ⊴ E×(E×E) ⊴ E×E ⊴ E`, using Goal 1 (applied twice, to peel off each product layer)
for the last two links. -/
theorem sum_trianglelefteq_of (hT : TD ⊴ E) (hArrow : funSpace E E ⊴ E) :
    sum E E hE hE ⊴ E := by
  have hPE : prod E E ⊴ E := prod_trianglelefteq_of hT hArrow
  exact trianglelefteq_trans
    (trianglelefteq_trans (sum_trianglelefteq_prodT hE) (prod_left_trianglelefteq (prod E E) hT))
    (trianglelefteq_trans (prod_right_trianglelefteq E hPE) hPE)

end Sum
end DomainTheory.NeighbourhoodSystems
