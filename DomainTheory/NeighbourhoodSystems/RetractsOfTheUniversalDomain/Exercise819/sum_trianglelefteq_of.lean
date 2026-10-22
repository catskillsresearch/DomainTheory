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
