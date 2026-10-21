/-ai
Each member of an indexed directed family of elements lies below the indexed directed union.

A neighbourhood of the member belongs to the union, with that index as the witness in the membership rule.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image
import all Mathlib.Data.Set.Image
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.Basic
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises.mem_iSupDirected

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

namespace NeighborhoodSystem


theorem le_iSupDirected {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) (i : I) :
    a i ≤ iSupDirected a hdir :=
  fun _ hZ => (mem_iSupDirected a hdir).mpr ⟨i, hZ⟩

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
