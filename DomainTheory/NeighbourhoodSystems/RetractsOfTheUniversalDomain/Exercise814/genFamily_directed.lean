/-ai
The generating family of a fixed point is directed.

For any two neighbourhood indices, the family of principal approximants supplies a common upper index, and the element map of the closure is monotone.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.BasicInst34
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.genFamily
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.IsClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : IsClosureOperator a)

theorem genFamily_directed (y : FixSet a) :
    ∀ i j : {X : Set α // y.1.mem X}, ∃ k, (genFamily h y i).1 ≤ (genFamily h y k).1 ∧
      (genFamily h y j).1 ≤ (genFamily h y k).1 := by
  intro i j
  obtain ⟨k, hik, hjk⟩ := principalFamily_directed y.1 i j
  exact ⟨k, a.toElementMap_mono hik, a.toElementMap_mono hjk⟩

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
