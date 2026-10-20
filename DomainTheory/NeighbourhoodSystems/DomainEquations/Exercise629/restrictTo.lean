module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self

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

/-- The cylinder restricted to a list of coordinates `l` (master outside `l`). -/
def restrictTo (D : ∀ i, NeighborhoodSystem (α i)) (l : List ι) (X : ∀ i, Set (α i)) :
    ∀ j, Set (α j) := fun j => if j ∈ l then X j else (D j).master

end Iso

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
