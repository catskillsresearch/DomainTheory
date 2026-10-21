/-ai
The intersection of two product neighbourhoods is the product neighbourhood of the pointwise intersections.

Extensionality on a dependent pair, together with the definition of a product neighbourhood, identifies both sides with membership of the second component in the two coordinate sets.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}

/-- Product neighbourhoods intersect coordinatewise (Scott's (2)). -/
theorem iprodNbhd_inter (X X' : ∀ i, Set (α i)) :
    iprodNbhd X ∩ iprodNbhd X' = iprodNbhd (fun i => X i ∩ X' i) := by
  apply Set.ext; rintro ⟨i, a⟩; simp [iprodNbhd, Set.mem_inter_iff]

end Exercise629

end DomainTheory.NeighbourhoodSystems
