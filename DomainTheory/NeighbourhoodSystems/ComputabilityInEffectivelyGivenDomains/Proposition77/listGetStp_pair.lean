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
