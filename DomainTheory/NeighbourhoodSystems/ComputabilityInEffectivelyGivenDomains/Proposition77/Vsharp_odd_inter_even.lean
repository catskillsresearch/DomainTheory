/-ai
The intersection of the enumerated set at 2a+1 with the enumerated set at 2b+2 is empty.

Rewrite the two sets by the odd clause and the even clause, and apply the law that a zero embedding meets a paired embedding in the empty set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_odd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_even

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_odd_inter_even (a b : ℕ) :
    Vsharp D P (2 * a + 1) ∩ Vsharp D P (2 * b + 2) = ∅ := by
  rw [Vsharp_odd, Vsharp_even, embZero_inter_embPair]

end Proposition77

end DomainTheory.NeighbourhoodSystems
