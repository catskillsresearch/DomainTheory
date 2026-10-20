/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.none_not_mem_injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.some_mem_injI
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.index_of_some_mem_injI

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem injI_inter_same (i : ι) (X Y : Set (α i)) : injI i X ∩ injI i Y = injI i (X ∩ Y) := by
  apply Set.ext
  rintro (_ | ⟨k, a⟩)
  · constructor
    · rintro ⟨h, _⟩; exact absurd h none_not_mem_injI
    · intro h; exact absurd h none_not_mem_injI
  · constructor
    · rintro ⟨hx, hy⟩
      obtain rfl := index_of_some_mem_injI hx
      exact some_mem_injI.mpr ⟨some_mem_injI.mp hx, some_mem_injI.mp hy⟩
    · intro h
      obtain rfl := index_of_some_mem_injI h
      have h' := some_mem_injI.mp h
      exact ⟨some_mem_injI.mpr h'.1, some_mem_injI.mpr h'.2⟩

end Exercise629

end DomainTheory.NeighbourhoodSystems
