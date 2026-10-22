module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Setup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Dsys
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.mem_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.rho

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614

variable {α : Type w}

/-- Scott's relational description `X ρₙ Y ↔ ∃ z ∈ Tⁿ({Γ}), X ⊆ z ⊆ Y`. -/
theorem rho_rel (s : Setup.{w}) (n : ℕ) {X Y : Set s.Tok} :
    (rho s n).rel X Y ↔
      (colim s).mem X ∧ (colim s).mem Y ∧ ∃ z, (Dsys s n).mem z ∧ X ⊆ z ∧ z ⊆ Y := by
  unfold rho
  rw [comp_rel]
  constructor
  · rintro ⟨z, ⟨hcX, hDz, hXz⟩, _, hcY, hzY⟩
    exact ⟨hcX, hcY, z, hDz, hXz, hzY⟩
  · rintro ⟨hcX, hcY, z, hDz, hXz, hzY⟩
    exact ⟨z, ⟨hcX, hDz, hXz⟩, hDz, hcY, hzY⟩

end Theorem614

end DomainTheory.NeighbourhoodSystems
