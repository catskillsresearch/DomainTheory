/-ai
Over an infinite index, the element domain of the indexed smash product has at most one element.

Any two elements agree on every token set. A neighbourhood of either element equals the master, and the other element contains the master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finset.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.Basic
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise629.iotimes_only_master

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}


variable {D : ∀ i, NeighborhoodSystem (α i)}


/-- **Exercise 6.29 — the infinite smash collapses to one point.** Its element domain is a
singleton (`⊥` only), so `⊗` has no sensible infinitary generalization. -/
theorem iotimes_subsingleton [Infinite ι] (D : ∀ i, NeighborhoodSystem (α i)) :
    Subsingleton (iotimes D).Element := by
  refine ⟨fun x y => ?_⟩
  apply Element.ext
  intro W
  constructor
  · intro hx; rw [iotimes_only_master D W (x.sub hx)]; exact y.master_mem
  · intro hy; rw [iotimes_only_master D W (y.sub hy)]; exact x.master_mem

end Exercise629
end DomainTheory.NeighbourhoodSystems
