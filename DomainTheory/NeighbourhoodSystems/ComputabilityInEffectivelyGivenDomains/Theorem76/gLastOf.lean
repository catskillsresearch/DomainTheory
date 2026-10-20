module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

/-- The last index of the chain `a, full₀, full₁, …`. -/
def gLastOf : ℕ → List ℕ → ℕ
  | a, [] => a
  | _, (b :: rest) => gLastOf b rest

end DomainTheory.NeighbourhoodSystems
