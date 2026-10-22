module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.mem_gColim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Texp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Exp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.BasicInst28
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctor_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctorMap_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.rho

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

/-- Scott's relational description `A ρₙ E ↔ ∃ z ∈ Texpⁿ({Γ}), A ⊆ z ⊆ E`. -/
theorem rho_rel (n : ℕ) {A E : Set Str} :
    (rho hN n).rel A E ↔ (Exp N hN).sys.mem A ∧ (Exp N hN).sys.mem E ∧
      ∃ z, (gTower (Texp N) n).sys.mem z ∧ A ⊆ z ∧ z ⊆ E := by
  unfold rho
  rw [comp_rel]
  constructor
  · rintro ⟨z, hproj, hinj⟩
    rw [Subsystem.proj_rel] at hproj
    rw [Subsystem.inj_rel] at hinj
    obtain ⟨hcA, hTz, hAz⟩ := hproj
    obtain ⟨_, hcE, hzE⟩ := hinj
    exact ⟨hcA, hcE, z, hTz, hAz, hzE⟩
  · rintro ⟨hcA, hcE, z, hTz, hAz, hzE⟩
    exact ⟨z, by rw [Subsystem.proj_rel]; exact ⟨hcA, hTz, hAz⟩,
      by rw [Subsystem.inj_rel]; exact ⟨hTz, hcE, hzE⟩⟩

end Uniqueness

end Exercise619

end DomainTheory.NeighbourhoodSystems
