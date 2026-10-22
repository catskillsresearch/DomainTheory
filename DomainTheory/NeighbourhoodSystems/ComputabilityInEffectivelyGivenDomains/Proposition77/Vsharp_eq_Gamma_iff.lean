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
