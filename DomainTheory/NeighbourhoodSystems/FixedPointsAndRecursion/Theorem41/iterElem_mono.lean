module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.mem_iterElem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap
















/-- The approximants form an increasing chain: `n ≤ m ⟹ fⁿ(⊥) ⊑ fᵐ(⊥)`. -/
theorem iterElem_mono (f : ApproximableMap V V) {n m : ℕ} (hnm : n ≤ m) :
    f.iterElem n ≤ f.iterElem m := by
  intro X hX
  rw [mem_iterElem] at hX ⊢
  exact rel_master_mono f hnm hX

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
