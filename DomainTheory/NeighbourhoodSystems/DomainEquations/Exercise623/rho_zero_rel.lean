module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFix
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.mem_gColim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Texp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Texp_rooted
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Exp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.BasicInst28
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctor_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctorMap_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.rho
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.rho_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

/-- **`ρ₀ = ⊥`** (the generator `{Γ}` is one-point): `ρ₀` relates `A` only to the master. -/
theorem rho_zero_rel {A E : Set Str} :
    (rho hN 0).rel A E ↔ (Exp N hN).sys.mem A ∧ E = (Exp N hN).sys.master := by
  rw [rho_rel]
  constructor
  · rintro ⟨hcA, hcE, z, hz, _, hzE⟩
    have hzm : z = (Exp N hN).sys.master :=
      (hz : z = gFix (Texp N)).trans (gColim_master (Texp N) (Texp_rooted hN)).symm
    subst hzm
    exact ⟨hcA, Set.Subset.antisymm ((Exp N hN).sys.sub_master hcE) hzE⟩
  · rintro ⟨hcA, rfl⟩
    exact ⟨hcA, (Exp N hN).sys.master_mem, (Exp N hN).sys.master,
      gColim_master (Texp N) (Texp_rooted hN), (Exp N hN).sys.sub_master hcA, subset_rfl⟩

end Uniqueness

end Exercise619

end DomainTheory.NeighbourhoodSystems
