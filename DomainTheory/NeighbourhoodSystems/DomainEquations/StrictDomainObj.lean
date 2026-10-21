/-ai
A strict domain object is a token type together with a neighbourhood system on it in which every neighbourhood is nonempty.
ai-/
module


public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition63
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62C
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516

@[expose] public section

universe w

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

/-- An object of Scott's category (Exercise 6.19): a token type, a neighbourhood system on it, and the
standing assumption `∅ ∉ 𝒟` (every neighbourhood is non-empty). -/
structure StrictDomainObj : Type (w + 1) where
  /-- The token type. -/
  carrier : Type w
  /-- The neighbourhood system. -/
  sys : NeighborhoodSystem carrier
  /-- Scott's standing assumption `∅ ∉ 𝒟`. -/
  nonempty : ∀ X, sys.mem X → X.Nonempty

end DomainTheory.NeighbourhoodSystems
