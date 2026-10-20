module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

section IndexedProduct

variable [Nonempty ι]


section Iso

variable [DecidableEq ι]

omit [Nonempty ι] in
@[simp] theorem updTuple_apply_self (i : ι) (U : Set (α i)) : updTuple D i U i = U := by
  simp [updTuple]

end Iso

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
