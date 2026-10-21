/-ai
The supremum of a monotone chain of elements indexed by the natural numbers is their directed union. For any two indices the maximum is an upper bound, by monotonicity of the chain.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The sup of a monotone `ω`-chain, realized as a directed union (`max`-directedness). -/
def supChain (s : ℕ → V.Element) (hmono : Monotone s) : V.Element :=
  NeighborhoodSystem.iSupDirected s
    (fun i j => ⟨max i j, hmono (le_max_left i j), hmono (le_max_right i j)⟩)

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
