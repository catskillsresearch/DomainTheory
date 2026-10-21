/-ai
The updated tuple at an index i with value U is the family of master neighbourhoods with the value at i replaced by U.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.master

@[expose] public section

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

/-- The tuple that is `U` at coordinate `i` and the master elsewhere. -/
def updTuple (D : ∀ i, NeighborhoodSystem (α i)) (i : ι) (U : Set (α i)) : ∀ j, Set (α j) :=
  Function.update (fun j => (D j).master) i U

end Iso

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
