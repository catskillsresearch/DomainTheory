/-ai
If every neighbourhood of the underlying domain is nonempty, then an enumerated set of the section domain equals the master neighbourhood if and only if its index is 0.

If the index is 0, the zero clause gives the master neighbourhood. If the sets are equal, the index is 0, an odd successor, or an even successor. The odd value is a zero embedding, which is distinct from the master neighbourhood, and the even value is a paired embedding, which is likewise distinct from it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.nat_shape
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_odd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Vsharp_even

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

theorem Vsharp_eq_Gamma_iff (hD : ∀ X, D.mem X → X.Nonempty) (j : ℕ) :
    Vsharp D P j = Gamma D ↔ j = 0 := by
  constructor
  · intro h
    rcases nat_shape j with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rfl
    · rw [Vsharp_odd] at h; exact absurd h (embZero_ne_Gamma D hD (P.X a))
    · rw [Vsharp_even] at h; exact absurd h (embPair_ne_Gamma D hD _ _)
  · rintro rfl; exact Vsharp_zero P

end Proposition77

end DomainTheory.NeighbourhoodSystems
