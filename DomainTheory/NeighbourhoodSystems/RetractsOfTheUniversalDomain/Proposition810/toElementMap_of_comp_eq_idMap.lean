/-ai
If an approximable map j after a map i is the identity, then j after i returns every element of the domain.

Rewrite the double application as the composite, substitute the identity composite, and apply the identity map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- If `j ∘ i = I_D`, then `j(i(v)) = v` for every `v ∈ |D|`. -/
theorem toElementMap_of_comp_eq_idMap {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hji : j.comp i = idMap D) (v : D.Element) : j.toElementMap (i.toElementMap v) = v := by
  rw [← toElementMap_comp, hji, toElementMap_idMap]

end DomainTheory.NeighbourhoodSystems
