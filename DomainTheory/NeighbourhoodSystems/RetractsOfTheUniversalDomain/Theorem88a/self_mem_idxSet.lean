/-ai
Every index n belongs to its own index set.

Membership unfolds to the inclusion of e n in itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.splitChoice_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Basic.Countable.Defs
import all Mathlib.Basic.Countable.Defs
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.mem_idxSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

section Reencode

variable (e : ℕ → Set α)

/-- Every index belongs to its own `idxSet` (`e n ⊆ e n`) — so `idxSet e n` is always non-empty,
regardless of whether `e n` itself is empty. -/
theorem self_mem_idxSet (n : ℕ) : n ∈ idxSet e n := show e n ⊆ e n from subset_rfl

end Reencode

end DomainTheory.NeighbourhoodSystems
