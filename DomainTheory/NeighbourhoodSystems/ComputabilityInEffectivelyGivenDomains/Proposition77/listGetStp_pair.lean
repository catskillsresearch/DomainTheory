/-ai
On an explicit accumulator pairing a countdown with a value, the indexing step returns the pair of the decremented countdown and the selection of the current element when the countdown is one, and of the carried value otherwise.

Unfolding the step, the pairing projections expose the countdown, the value, and the current element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGetStp

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- The fold step on an explicit accumulator `pair cd val`. -/
theorem listGetStp_pair (cd val x : ℕ) :
    listGetStp (Nat.pair x (Nat.pair (Nat.pair cd val) 0))
      = Nat.pair (cd - 1) (selectFn (isOne cd) x val) := by
  unfold listGetStp
  simp only [unpair_pair_fst, unpair_pair_snd]

end Proposition77

end DomainTheory.NeighbourhoodSystems
