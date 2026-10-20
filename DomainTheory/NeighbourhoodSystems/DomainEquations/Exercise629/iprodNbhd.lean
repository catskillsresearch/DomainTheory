module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

/-- A **product neighbourhood** `iprodNbhd X = {⟨i, a⟩ ∣ a ∈ X i}` over `Σ i, α i`. -/
def iprodNbhd (X : ∀ i, Set (α i)) : Set (Σ i, α i) := {p | p.2 ∈ X p.1}

end Exercise629

end DomainTheory.NeighbourhoodSystems
