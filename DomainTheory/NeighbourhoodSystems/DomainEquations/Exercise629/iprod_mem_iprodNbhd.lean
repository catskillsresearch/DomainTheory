/-ai
If each set of a family is a neighbourhood and the family is finitely supported, then the product neighbourhood of the family is a neighbourhood of the indexed product.

The family itself is the witnessing tuple.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}







variable {D : ∀ i, NeighborhoodSystem (α i)}




section IndexedProduct

variable [Nonempty ι]


theorem iprod_mem_iprodNbhd {X : ∀ i, Set (α i)} (hX : ∀ i, (D i).mem (X i))
    (hXf : FinSupp D X) : (iprod D).mem (iprodNbhd X) :=
  ⟨X, hX, hXf, rfl⟩

end IndexedProduct
end Exercise629
end DomainTheory.NeighbourhoodSystems
