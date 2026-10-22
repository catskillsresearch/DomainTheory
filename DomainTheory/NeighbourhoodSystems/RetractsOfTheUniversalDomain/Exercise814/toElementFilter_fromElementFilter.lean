/-ai
The composite of the forward map after the backward map is the identity on elements of the domain reconstructed from a closure.

Two elements are equal when they contain the same neighbourhoods. If a principal up-set of a compact lies below the backward image, compactness of that compact against the directed family of confirmed indices produces one confirmed index above it, and the original element is closed upward under the antitone comparison of up-sets. Conversely, a neighbourhood of the original element is the up-set of some compact belonging to the element, and that compact is a confirmed index, so it lies below the directed supremum.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.upFix_antitone
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.domainOfClosure
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.toElementFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.confirmedIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.BasicInst34
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.confirmedIdx_directed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.fromElementFilter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : ClosureOperator a)

theorem toElementFilter_fromElementFilter (g : (domainOfClosure h).Element) :
    toElementFilter h (fromElementFilter h g) = g := by
  apply Element.ext
  intro S
  constructor
  · rintro ⟨k0, rfl, hk0⟩
    obtain ⟨i, hi⟩ := k0.2 (fun i : confirmedIdx h g => i.1.1) (confirmedIdx_directed h g) hk0
    exact g.up_mem i.2 ⟨k0, rfl⟩ (upFix_antitone h hi)
  · intro hS
    obtain ⟨k0, rfl⟩ := g.sub hS
    exact ⟨k0, rfl, le_iSupDirected _ (confirmedIdx_directed h g) ⟨k0, hS⟩⟩

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
