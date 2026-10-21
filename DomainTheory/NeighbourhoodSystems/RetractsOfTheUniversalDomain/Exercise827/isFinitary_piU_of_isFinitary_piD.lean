/-ai
If the product of d on the function space is finitary, then the product regarded as a self-map of the universal domain is finitary.

Finitariness supplies a domain and an order isomorphism of its elements with the fixed points of the function-space product. Transport that isomorphism along the order isomorphism of the fixed points of the universal-domain product with those fixed points.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise826
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap





































/-- **Exercise 8.27(b)(0), corollary: if `piD d` is finitary then so is `piU d`.** Mirrors
`isFinitary_subU`'s use of `subUFixIso`. This is the reduction Exercise 8.27(b)(1)–(b)(4) will
target: it suffices to prove `IsFinitary (piD d)` for `d` polymorphic. -/
theorem isFinitary_piU_of_isFinitary_piD {d : ApproximableMap U U} (h : IsFinitary (piD d)) :
    IsFinitary (piU d) := by
  obtain ⟨β, F, ⟨iso⟩⟩ := h
  exact ⟨β, F, ⟨(piUFixIso d).trans iso⟩⟩

end DomainTheory.NeighbourhoodSystems
