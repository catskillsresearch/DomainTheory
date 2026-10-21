/-ai
Every approximant of an approximable endomap, starting from bottom, lies below the least fixed point.

A neighbourhood of the approximant belongs, by the membership law for approximants, to the least fixed point at that index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise411.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- `fⁿ(⊥) ⊑ fix(f)`: every approximant lies below the least fixed point. -/
theorem iterElem_le_fixElement (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem n ≤ f.fixElement :=
  fun _ hX => ⟨n, (mem_iterElem f n).mp hX⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
