/-ai
Looking up index i in the code of a list returns the defaulted entry of that list at i.

Unfolding the lookup, the fold of a code equals the corresponding list fold, and that fold reads off the entry.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGet_foldl

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **Correctness of `listGet`** on a coded list. -/
theorem listGet_encodeList (l : List ℕ) (i : ℕ) : listGet (encodeList l) i = l.getD i 0 := by
  unfold listGet
  rw [foldCode_eq]
  exact listGet_foldl l i 0

end Proposition77

end DomainTheory.NeighbourhoodSystems
