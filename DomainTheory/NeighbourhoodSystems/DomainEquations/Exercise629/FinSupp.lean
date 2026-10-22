/-ai
A family of token sets has finite support when some list of indices contains every index at which the set fails to be the master of its system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

variable {D : ∀ i, NeighborhoodSystem (α i)}

/-- **Choice-free finite support**: a *list* enumerating all coordinates where `X` is non-master.
(Mathlib's `Set.Finite` is built on `Fintype` and pulls in `Classical.choice`; a `List` witness keeps
the construction constructive, which is exactly what is needed for the cylinder.) -/
def FinSupp (D : ∀ i, NeighborhoodSystem (α i)) (X : ∀ i, Set (α i)) : Prop :=
  ∃ l : List ι, ∀ i, i ∉ l → X i = (D i).master

end Exercise629

end DomainTheory.NeighbourhoodSystems
