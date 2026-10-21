/-ai
The remainder of a state packed from a remainder, a positive code, a negative code, and a U-code is that remainder.

Unfolding the remainder projection and the packing, the left-unpairing equation yields the first component.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.stateRem
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.packState

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

section AtomCode

variable {E : NeighborhoodSystem α} (Q : ComputablePresentation E)

@[simp] theorem stateRem_packState (a b c d : ℕ) : stateRem (packState a b c d) = a := by
  unfold stateRem packState; simp only [unpair_pair_fst]

end AtomCode

end DomainTheory.NeighbourhoodSystems
