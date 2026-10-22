/-ai
The embedded set of index n is nonempty.

The index n belongs to the set of all indices and to its own index set, so the nonemptiness law of Scott's sequence applies.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.splitChoice_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Basic.Countable.Defs
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.mem_idxSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.self_mem_idxSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.univ_nonempty_nat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Yidx

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

/-- **`Yidx e n` is always non-empty** (hence, by `Yidx_empty_or_mem`, always a genuine
`U`-neighbourhood): `n` itself witnesses `n ∈ idxSet e n`. -/
theorem Yidx_nonempty (n : ℕ) : (Yidx e n).Nonempty :=
  Yseq_nonempty_of_mem splitChoice (idxSet e) Set.univ univ_nonempty_nat splitChoice_isSplitSpec
    (Set.mem_univ n) (self_mem_idxSet e n)

end Setup

end DomainTheory.NeighbourhoodSystems
