module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

/-- The consecutive `g`-steps `g.rel (X_a) (X_{full₀})`, `g.rel (X_{full₀}) (X_{full₁})`, … all hold. -/
def gStepsOK (g : ApproximableMap V V) (P : ComputablePresentation V) : ℕ → List ℕ → Prop
  | _, [] => True
  | a, (b :: rest) => g.rel (P.X a) (P.X b) ∧ gStepsOK g P b rest

end DomainTheory.NeighbourhoodSystems
