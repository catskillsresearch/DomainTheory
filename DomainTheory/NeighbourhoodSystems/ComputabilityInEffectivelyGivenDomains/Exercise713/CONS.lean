/-ai
Two indices are consistent when some index is included in both of them.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise713.InclStructure

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise713

open NeighborhoodSystem Domain.Recursive

namespace InclStructure

variable (I : InclStructure)

/-- Scott's consistency relation `CONS(n, m) :↔ ∃ k. INCL(k, n) ∧ INCL(k, m)`. -/
def CONS (n m : ℕ) : Prop := ∃ k, I.INCL k n ∧ I.INCL k m

end InclStructure

end DomainTheory.NeighbourhoodSystems.Exercise713
