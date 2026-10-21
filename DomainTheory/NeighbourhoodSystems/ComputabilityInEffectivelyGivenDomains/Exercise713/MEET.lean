/-ai
An index k is a meet of indices n and m when, for every index j, j is included in k if and only if j is included in both n and m.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

namespace InclStructure

variable (I : InclStructure)

/-- Scott's binary-meet relation `MEET(n, m, k) :↔ ∀ j. (INCL(j, k) ↔ INCL(j, n) ∧ INCL(j, m))`. -/
def MEET (n m k : ℕ) : Prop := ∀ j, I.INCL j k ↔ (I.INCL j n ∧ I.INCL j m)

end InclStructure

end DomainTheory.NeighbourhoodSystems.Exercise713
