module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.some_mem_injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.sumMasterI

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem injI_subset_sumMasterI {i : ι} {X : Set (α i)} (hX : (D i).mem X) :
    injI i X ⊆ sumMasterI D := by
  rintro w ⟨a, ha, rfl⟩
  exact Set.mem_insert_iff.mpr (Or.inr ⟨⟨i, a⟩, (D i).sub_master hX ha, rfl⟩)

end Exercise629

end DomainTheory.NeighbourhoodSystems
