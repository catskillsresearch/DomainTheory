/-ai
The element assembled from a tuple of components contains the slice of a set U at an index i if and only if the i-th component contains U.

If the assembled element contains the slice, the witnessing tuple equals the one-coordinate update of U at i, by injectivity of product neighbourhoods, and the i-th component of that update is U. Conversely, that update lies in every component, is supported by the singleton list of i, and presents the slice.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.mem_iprodNbhd
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iprodNbhd_injective
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_self
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.updTuple_apply_ne
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.slice
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.fromPi

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

theorem fromPi_mem_slice (x : ∀ i, (D i).Element) (i : ι) (U : Set (α i)) :
    (fromPi D x).mem (slice D i U) ↔ (x i).mem U := by
  constructor
  · rintro ⟨X, hX, _, heq⟩
    have hXeq : updTuple D i U = X := iprodNbhd_injective heq
    have hi := hX i
    rwa [← hXeq, updTuple_apply_self] at hi
  · intro hU
    refine ⟨updTuple D i U, fun j => ?_, ⟨[i], fun j hj => ?_⟩, rfl⟩
    · by_cases h : j = i
      · subst h; rw [updTuple_apply_self]; exact hU
      · rw [updTuple_apply_ne U h]; exact (x j).master_mem
    · exact updTuple_apply_ne U fun h => hj (List.mem_singleton.mpr h)

end Iso

end IndexedProduct

end Exercise629

end DomainTheory.NeighbourhoodSystems
