/-ai
The embedded set of index n is empty or a neighbourhood of U.

This is the empty-or-neighbourhood law of Scott's sequence, applied to the index sets, the nonempty set of all indices, and the splitting specification of the total choice.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.univ_nonempty_nat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Yidx

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

/-- `Yidx e n` is always `∅` or a genuine `U`-neighbourhood. -/
theorem Yidx_empty_or_mem (n : ℕ) : Yidx e n = ∅ ∨ U.mem (Yidx e n) :=
  Yseq_empty_or_mem splitChoice (idxSet e) Set.univ univ_nonempty_nat splitChoice_isSplitSpec n

end Setup

end DomainTheory.NeighbourhoodSystems
