/-ai
The successor of the n-th tower system is the transport, along the carrier identification of that level, of the image of that level under T.

The equality is definitional.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Setup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dceq

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614

variable {α : Type w}

/-- `Tⁿ⁺¹({Γ})` is the carrier-transport of `T(Tⁿ({Γ}))`. -/
theorem Dsys_succ (s : Setup.{w}) (n : ℕ) :
    Dsys s (n + 1) = (Dceq s n ▸ (s.T.obj ⟨s.Tok, Dsys s n⟩).sys : NeighborhoodSystem s.Tok) :=
  rfl

end Theorem614

end DomainTheory.NeighbourhoodSystems
