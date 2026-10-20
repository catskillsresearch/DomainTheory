module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- Under `∅ ∉ 𝒟`, no `V k` is empty. -/
theorem Vsharp_nonempty (hD : ∀ X, D.mem X → X.Nonempty) (k : ℕ) : (Vsharp D P k).Nonempty :=
  memS_nonempty hD (Vsharp_mem P k)

end Proposition77

end DomainTheory.NeighbourhoodSystems
