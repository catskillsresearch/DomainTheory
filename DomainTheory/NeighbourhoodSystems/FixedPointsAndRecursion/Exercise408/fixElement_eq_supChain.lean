/-ai
The least fixed point of an approximable endomap f equals the supremum of the monotone chain of its approximants from bottom.

Extensionality of elements reduces the equality to membership of an arbitrary neighbourhood. Membership in the supremum and membership in the least fixed point are each the existence of an index, and the membership law for approximants converts a witness in either direction.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise408.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise408.mem_supChain
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise408.iterElem_monotone

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.mem_iterElem
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- The approximants `fⁿ(⊥)` form a monotone chain whose sup is `fix(f)`. -/
theorem fixElement_eq_supChain (f : ApproximableMap V V) :
    f.fixElement = supChain f.iterElem (iterElem_monotone f) := by
  apply Element.ext
  intro X
  rw [mem_supChain, mem_fixElement]
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_iterElem f n).mpr hn⟩
  · rintro ⟨n, hn⟩; exact ⟨n, (mem_iterElem f n).mp hn⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
