/-ai
Bit-sources that agree on every bit below depth n have the same emptiness flag at that depth.

State congruence gives equal positive and negative codes, and the flag is the decider on that pair.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


theorem atomUEmpty_congr {n k k' : ℕ} (h : ∀ i < n, deltaOf k i = deltaOf k' i) :
    atomUEmpty P n k = atomUEmpty P n k' := by
  obtain ⟨hpos, hneg, -⟩ := atomUCodeState_congr P h
  unfold atomUEmpty
  rw [hpos, hneg]

end DomainTheory.NeighbourhoodSystems
