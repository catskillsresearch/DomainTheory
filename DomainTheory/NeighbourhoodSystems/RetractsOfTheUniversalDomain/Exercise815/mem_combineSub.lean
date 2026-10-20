module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.combineSub

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section FinGen

variable (P : ComputablePresentation D)

section Combine

variable (js sub1 sub2 : List ℕ)

variable {js sub1 sub2}

theorem mem_combineSub {j : ℕ} :
    j ∈ combineSub js sub1 sub2 ↔ j ∈ js ∧ (j ∈ sub1 ∨ j ∈ sub2) := by
  unfold combineSub
  rw [List.mem_filter, decide_eq_true_iff]

end Combine

end FinGen

end DomainTheory.NeighbourhoodSystems
