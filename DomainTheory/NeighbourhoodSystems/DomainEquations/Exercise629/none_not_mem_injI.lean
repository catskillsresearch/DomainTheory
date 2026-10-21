/-ai
The basepoint belongs to no tagged copy.

A member of a tagged copy is the tag of some token, and simplifying the resulting equation rules out the basepoint.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.injI

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

theorem none_not_mem_injI {i : ι} {X : Set (α i)} : (none : Option (Σ i, α i)) ∉ injI i X := by
  rintro ⟨a, _, heq⟩; simp at heq

end Exercise629

end DomainTheory.NeighbourhoodSystems
