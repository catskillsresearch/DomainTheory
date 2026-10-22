/-ai
The universe of natural numbers is nonempty.

Zero belongs to it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.splitChoice_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Basic.Countable.Defs
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.mem_idxSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

/-- `Δ' := Set.univ` is always non-empty, so the general `Yseq`/transfer apparatus of
`Theorem88.lean` applies to `(idxSet e, Set.univ)` unconditionally — no `∅`-freeness hypothesis on
`D` is ever needed, since we reindexed onto `ℕ` before invoking it (`idxSet_nonempty`). -/
theorem univ_nonempty_nat : (Set.univ : Set ℕ).Nonempty := ⟨0, trivial⟩

end Setup

end DomainTheory.NeighbourhoodSystems
