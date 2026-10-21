/-ai
The enumerated set at index 2n+1 is the zero embedding of the enumerated neighbourhood of n.

Apply the successor clause. The index is odd, so the first branch applies, and half of 2n equals n.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_succ

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_odd (n : ℕ) : Vsharp D P (2 * n + 1) = embZero (P.X n) := by
  rw [Vsharp_succ, ite_eq_left (by omega), show 2 * n / 2 = n from by omega]

end Proposition77

end DomainTheory.NeighbourhoodSystems
