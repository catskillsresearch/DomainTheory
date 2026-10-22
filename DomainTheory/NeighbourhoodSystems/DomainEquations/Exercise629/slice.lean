/-ai
The slice of a set U at an index i is the product neighbourhood of the tuple that equals U at i and equals the master at every other index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self

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

/-- The slice cylinder: `U` at coordinate `i`, master elsewhere. -/
def slice (D : ∀ i, NeighborhoodSystem (α i)) (i : ι) (U : Set (α i)) : Set (Σ i, α i) :=
  iprodNbhd (updTuple D i U)

end Iso

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
