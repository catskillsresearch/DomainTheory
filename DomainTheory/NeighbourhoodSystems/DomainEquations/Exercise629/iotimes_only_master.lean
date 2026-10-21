/-ai
Over an infinite index, every neighbourhood of the indexed smash product equals its master.

Such a neighbourhood is the master already, or it is the product neighbourhood of a tuple that differs from the master at every index and is supported by a finite list. Every index then lies on that list, so the set of entries of the list contains the whole index type, which is infinite.
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




















/-- **Exercise 6.29 — `⊗` does not generalize.** Over an infinite index, the smash product has only
its basepoint: an all-coordinates-proper cylinder has support `Set.univ`, which cannot be finite. -/
theorem iotimes_only_master [Infinite ι] (D : ∀ i, NeighborhoodSystem (α i)) :
    ∀ W, (iotimes D).mem W → W = (iotimes D).master := by
  rintro W (rfl | ⟨X, _, hXne, ⟨l, hl⟩, rfl⟩)
  · rfl
  · -- Every coordinate is proper, so the finite support list `l` would have to contain *all* of `ι`,
    -- impossible for an infinite index. This is a cardinality argument: Prop-level and unavoidably
    -- classical (Mathlib's `Set.Finite`/`Fintype` API is built on `Classical.choice`).
    refine absurd ((List.finite_toSet l).subset (fun i _ => ?_)) Set.infinite_univ
    exact not_not.mp fun hni => hXne i (hl i hni)

end Exercise629
end DomainTheory.NeighbourhoodSystems
