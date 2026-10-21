/-ai
If e i ∩ e j = e m, then the intersection of the index sets of i and j is the index set of m.

Extensionality reduces the claim to the equivalence of e k ⊆ e i and e k ⊆ e j with e k ⊆ e m. The two inclusions are containment in the intersection, and the hypothesis rewrites that intersection as e m.
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

/-- If `e i ∩ e j = e m` (i.e. `{e i, e j}` is witnessed-consistent, with witness realizing the
intersection exactly as `e m`), then `idxSet e i ∩ idxSet e j = idxSet e m` — a **definitional**
rewriting of the set-builder, needing no transfer at all. -/
theorem idxSet_inter_of_inter_eq {i j m : ℕ} (h : e i ∩ e j = e m) :
    idxSet e i ∩ idxSet e j = idxSet e m := by
  ext k
  show e k ⊆ e i ∧ e k ⊆ e j ↔ e k ⊆ e m
  rw [← Set.subset_inter_iff, h]

end Reencode

end DomainTheory.NeighbourhoodSystems
