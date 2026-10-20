module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Setup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.iter
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614

variable {α : Type w}

/-- The basic subdomain step `Tⁿ({Γ}) ◁ Tⁿ⁺¹({Γ})`. -/
theorem Dchain (s : Setup.{w}) (n : ℕ) : Dsys s n ◁ Dsys s (n + 1) := (iter s n).2.2

end Theorem614

end DomainTheory.NeighbourhoodSystems
