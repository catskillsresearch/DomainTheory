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


theorem iSupDirected_le {α : Type*} {V : NeighborhoodSystem α} {I : Type*} [Nonempty I]
    (a : I → V.Element) (hdir : ∀ i j, ∃ k, a i ≤ a k ∧ a j ≤ a k) {y : V.Element}
    (hy : ∀ i, a i ≤ y) : iSupDirected a hdir ≤ y := by
  intro Z hZ
  obtain ⟨i, hi⟩ := (mem_iSupDirected a hdir).mp hZ
  exact hy i Z hi

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
