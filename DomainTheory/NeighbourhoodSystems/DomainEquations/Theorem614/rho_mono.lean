module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Setup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.chain_le
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.mem_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.rho
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.rho_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614

variable {α : Type w}

/-- `ρₙ ⊆ ρₘ` for `n ≤ m` (the projection chain is increasing). -/
theorem rho_mono (s : Setup.{w}) {n m : ℕ} (h : n ≤ m) {X Y : Set s.Tok}
    (hr : (rho s n).rel X Y) : (rho s m).rel X Y := by
  rw [rho_rel] at hr ⊢
  obtain ⟨hcX, hcY, z, hDz, hXz, hzY⟩ := hr
  exact ⟨hcX, hcY, z, (chain_le s h).sub hDz, hXz, hzY⟩

end Theorem614

end DomainTheory.NeighbourhoodSystems
