/-ai
A list of indices is a valid chain of steps for a map from a starting index when the list is empty, and when the map relates the neighbourhood at the current index to the neighbourhood at the head and the tail is a valid chain from the head.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

/-- The consecutive `g`-steps `g.rel (X_a) (X_{full₀})`, `g.rel (X_{full₀}) (X_{full₁})`, … all hold. -/
def gStepsOK (g : ApproximableMap V V) (P : ComputablePresentation V) : ℕ → List ℕ → Prop
  | _, [] => True
  | a, (b :: rest) => g.rel (P.X a) (P.X b) ∧ gStepsOK g P b rest

end DomainTheory.NeighbourhoodSystems
