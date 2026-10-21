/-ai
Extending an index list along a sublist enlarges its finitely generated subsystem.

A sublist that witnesses membership for the smaller list remains a sublist of the larger list.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition611
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise714
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise815.finGen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

section FinGen

variable (P : ComputablePresentation D)

/-- **Monotonicity.** A sublist generates a smaller (or equal) finitely generated subsystem. -/
theorem finGen_mono {js js' : List ℕ} (h : js.Sublist js') : finGen P js ⊆ finGen P js' :=
  fun _ ⟨sub, hsub, hD, hY⟩ => ⟨sub, hsub.trans h, hD, hY⟩

end FinGen

end DomainTheory.NeighbourhoodSystems
