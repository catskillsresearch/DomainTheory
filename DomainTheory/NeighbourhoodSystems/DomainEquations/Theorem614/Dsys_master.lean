/-ai
Every system in the tower has the same master as the generating system.

The proof is by induction on the level. The zeroth level is the generating system. At a successor, the subdomain step identifies the master of the successor with the master of the previous level, and the inductive hypothesis replaces that master by the generating master.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Setup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dchain

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614

variable {α : Type w}

/-- Every system in the tower has the same master `Δ = Γ`. -/
theorem Dsys_master (s : Setup.{w}) (n : ℕ) : (Dsys s n).master = s.Γ.master := by
  induction n with
  | zero => rfl
  | succ k ih => rw [← (Dchain s k).master_eq]; exact ih

end Theorem614

end DomainTheory.NeighbourhoodSystems
