module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

namespace InclStructure

variable (I : InclStructure)

/-- The hint neighbourhood `Sₙ = {m ∣ INCL(m, n)}` over the token type `ℕ`. -/
def toNbhd (n : ℕ) : Set ℕ := {m | I.INCL m n}

end InclStructure

end DomainTheory.NeighbourhoodSystems.Exercise713
