module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.self_mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.domainOfClosure
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.confirmedIdx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.BasicInst34
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.IsClosureOperator

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : IsClosureOperator a)

theorem confirmedIdx_directed (g : (domainOfClosure h).Element) :
    ∀ i j : confirmedIdx h g, ∃ k : confirmedIdx h g,
      i.1.1.1 ≤ k.1.1.1 ∧ j.1.1.1 ≤ k.1.1.1 := by
  rintro ⟨k1, hk1⟩ ⟨k2, hk2⟩
  have hint : g.mem (upFix h k1 ∩ upFix h k2) := g.inter_mem hk1 hk2
  obtain ⟨k3, hk3eq⟩ := g.sub hint
  rw [hk3eq] at hint
  have hmem3 : k3 ∈ upFix h k1 ∩ upFix h k2 := hk3eq ▸ self_mem_upFix h k3
  exact ⟨⟨k3, hint⟩, hmem3.1, hmem3.2⟩

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
