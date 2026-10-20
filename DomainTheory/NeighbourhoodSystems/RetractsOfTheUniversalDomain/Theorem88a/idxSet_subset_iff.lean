module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.splitChoice_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Basic.Countable.Defs
import all Mathlib.Basic.Countable.Defs
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.idxSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.mem_idxSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.self_mem_idxSet

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

section Reencode

variable (e : ℕ → Set α)

/-- The raw inclusion order on `idxSet`s matches `e`'s own inclusion order — this is the
"separation" property `D†` is built to have. -/
theorem idxSet_subset_iff (i j : ℕ) : idxSet e i ⊆ idxSet e j ↔ e i ⊆ e j :=
  ⟨fun h => h (self_mem_idxSet e i), fun h _ hm => hm.trans h⟩

end Reencode

end DomainTheory.NeighbourhoodSystems
