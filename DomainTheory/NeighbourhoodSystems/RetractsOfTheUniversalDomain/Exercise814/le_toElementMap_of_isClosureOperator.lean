module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section ClosureOperator

variable {a : ApproximableMap E E}

/-- Unfolding `I_E ⊑ a` at the element level (Theorem 3.13(i)): `y ⊑ a(y)` for every `y`. -/
theorem le_toElementMap_of_isClosureOperator (h : ClosureOperator a) (y : E.Element) :
    y ≤ a.toElementMap y := by
  have h1 := (le_iff_toElementMap_le.mp h.out.2) y
  rwa [toElementMap_idMap] at h1

end ClosureOperator

end DomainTheory.NeighbourhoodSystems
