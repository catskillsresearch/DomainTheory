/-ai
The neighbourhood e i is contained in e j if and only if the transferred neighbourhood Yidx e i is contained in Yidx e j.

Rewrite the neighbourhood inclusion as the corresponding inclusion of index sets. The transfer lemma for inclusions, applied to the chosen splitting, the index sets, and the universe, yields the inclusion of the transferred neighbourhoods once the intersections with the universe are removed. Those intersections are redundant: intersecting with the universe does nothing, and Yidx e i is already contained in the master neighbourhood.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet_subset_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.univ_nonempty_nat
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Yidx
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Yidx_subset_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

section Setup

variable (D : NeighborhoodSystem α) (e : ℕ → Set α)
  (hcover : ∀ S, D.mem S ↔ ∃ n, S = e n) (he0 : e 0 = D.master)

/-- **The order-embedding at the neighbourhood level.** This is where the whole `idxSet`
reindexing pays off: because `idxSet`'s inclusion order matches `e`'s (`idxSet_subset_iff`), the
generic `transfer_subset_iff` (with `Δ' = Set.univ`, so the `Δ' ∩ ·`/`U.master ∩ ·` wrappers are
trivial since `Yidx e i ⊆ U.master` always) yields exactly Scott's matching invariant restricted to
plain inclusion. -/
theorem embed_subset_iff (i j : ℕ) : e i ⊆ e j ↔ Yidx e i ⊆ Yidx e j := by
  rw [← idxSet_subset_iff e i j]
  have := transfer_subset_iff splitChoice (idxSet e) Set.univ univ_nonempty_nat
    splitChoice_isSplitSpec i j
  rwa [Set.univ_inter, Set.inter_eq_self_of_subset_right (Yidx_subset_master e i)] at this

end Setup

end DomainTheory.NeighbourhoodSystems
