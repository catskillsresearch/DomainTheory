/-ai
The carrier of the image under T of the n-th system of the tower is the token type of the generating system.

This is the carrier component of the iteration at that level.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Setup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.iter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614

variable {α : Type w}

/-- The carrier identification `(T.obj Tⁿ({Γ})).carrier = Tok`. -/
theorem Dceq (s : Setup.{w}) (n : ℕ) : (s.T.obj ⟨s.Tok, Dsys s n⟩).carrier = s.Tok := (iter s n).2.1

end Theorem614

end DomainTheory.NeighbourhoodSystems
