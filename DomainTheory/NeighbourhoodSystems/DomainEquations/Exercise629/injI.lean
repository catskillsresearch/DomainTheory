/-ai
The tagged copy of a set X at an index i is the image of X under the map sending a token to the optional dependent pair given by tagging the pair of i with that token.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- A tagged copy `inj i X = {some ⟨i, a⟩ ∣ a ∈ X}` of summand `i`. -/
def injI (i : ι) (X : Set (α i)) : Set (Option (Σ i, α i)) :=
  (fun a => (some ⟨i, a⟩ : Option (Σ i, α i))) '' X

end Exercise629

end DomainTheory.NeighbourhoodSystems
