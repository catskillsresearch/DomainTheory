module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77











variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)













































variable (fcons feq finter : ℕ → ℕ)















/-- **Proposition 7.7 (Scott 1981, PRG-19).** If `D` is effectively given, so is `D^§`. -/
theorem dsharp_isEffectivelyGiven (P : ComputablePresentation D)
    (hD : ∀ X, D.mem X → X.Nonempty) :
    (Dsharp D hD).IsEffectivelyGiven :=
  ⟨dsharpPresentation P hD⟩

end Proposition77
end DomainTheory.NeighbourhoodSystems
