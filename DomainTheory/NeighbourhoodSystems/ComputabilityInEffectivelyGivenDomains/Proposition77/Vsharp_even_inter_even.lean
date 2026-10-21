/-ai
The intersection of the enumerated sets at 2a+2 and at 2b+2 is the paired embedding of the two componentwise intersections of the unpaired indices.

Rewrite both sets by the even clause and apply the intersection law for paired embeddings.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_even

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_even_inter_even (a b : ℕ) :
    Vsharp D P (2 * a + 2) ∩ Vsharp D P (2 * b + 2)
      = embPair (Vsharp D P a.unpair.1 ∩ Vsharp D P b.unpair.1)
                (Vsharp D P a.unpair.2 ∩ Vsharp D P b.unpair.2) := by
  rw [Vsharp_even, Vsharp_even, embPair_inter]

end Proposition77

end DomainTheory.NeighbourhoodSystems
