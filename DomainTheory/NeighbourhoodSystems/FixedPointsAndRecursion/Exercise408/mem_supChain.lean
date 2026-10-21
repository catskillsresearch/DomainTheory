/-ai
A neighbourhood belongs to the supremum of a monotone chain of elements if and only if it belongs to some term of the chain.

This is the membership law for the directed union that defines the supremum.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise408.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


theorem mem_supChain (s : ℕ → V.Element) (hmono : Monotone s) {Z : Set α} :
    (supChain s hmono).mem Z ↔ ∃ n, (s n).mem Z :=
  NeighborhoodSystem.mem_iSupDirected s _

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
