/-ai
The combined sub-selection of an index list, relative to two further lists, retains those entries that lie in the first list or the second.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section FinGen

variable (P : ComputablePresentation D)

section Combine

variable (js sub1 sub2 : List ℕ)

/-- The sub-selection of `js` consisting of entries belonging to `sub1` or `sub2` — the `List`-level
"join" of two sub-selections, used to combine two consistent sub-meets into a third. -/
def combineSub : List ℕ := js.filter (fun j => decide (j ∈ sub1 ∨ j ∈ sub2))

end Combine

end FinGen

end DomainTheory.NeighbourhoodSystems
