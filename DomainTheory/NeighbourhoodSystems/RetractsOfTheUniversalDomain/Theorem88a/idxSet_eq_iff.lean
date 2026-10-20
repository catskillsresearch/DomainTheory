module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.splitChoice_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Basic.Countable.Defs
import all Mathlib.Basic.Countable.Defs
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88a.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

section Reencode

variable (e : ℕ → Set α)





theorem idxSet_eq_iff (i j : ℕ) : idxSet e i = idxSet e j ↔ e i = e j :=
  ⟨fun h => Set.Subset.antisymm ((idxSet_subset_iff e i j).mp h.subset)
      ((idxSet_subset_iff e j i).mp h.symm.subset),
    fun h => by rw [idxSet, idxSet, h]⟩

end Reencode
end DomainTheory.NeighbourhoodSystems
