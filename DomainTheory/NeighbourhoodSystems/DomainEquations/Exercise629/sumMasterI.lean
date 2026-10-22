/-ai
The sum master of a family of neighbourhood systems is the set of optional dependent pairs obtained by inserting the basepoint into the set of tags of tokens from the product neighbourhood of the family of masters.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.some_mem_injI

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- The basepoint master of the indexed sum: `{none} ∪ {some ⟨i, a⟩ ∣ a ∈ Δᵢ}`. -/
def sumMasterI (D : ∀ i, NeighborhoodSystem (α i)) : Set (Option (Σ i, α i)) :=
  insert none ((fun p => (some p : Option (Σ i, α i))) '' iprodNbhd (fun i => (D i).master))

end Exercise629

end DomainTheory.NeighbourhoodSystems
