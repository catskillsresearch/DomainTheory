/-ai
The underlying map of any homomorphism from Exp to an algebra equals the evaluation map, so the evaluation homomorphism is the unique homomorphism.

The composite of the homomorphism with the union of the projections equals the evaluation map: by extensionality, a factorisation through some projection is a pair in the corresponding Kleene iterate, using that the homomorphism after that projection equals the iterate, and conversely. The homomorphism equals that composite because the union of the projections is the identity on Exp.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.mem_gColim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.ext
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.BasicInst28
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctor_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctorMap_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.ExpAlg
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descMap
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.iSupRho
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.iSupRho_eq_id
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gcomp_rho_eq
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.TexpF

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

variable (B : TAlgebra (TexpF N))

/-- **The underlying map of any homomorphism `g : Exp → D` is `val = descMap`.** Hence `descAlgHom`
is the *unique* homomorphism. -/
theorem descMap_eq_algHom (g : AlgHom (ExpAlg N hN) B) : g.hom.1 = descMap hN B := by
  have hcomp : g.hom.1.comp (iSupRho hN) = descMap hN B := by
    apply ApproximableMap.ext
    intro A E
    rw [comp_rel, descMap_rel]
    constructor
    · rintro ⟨Y, ⟨n, hrho⟩, hg⟩
      refine ⟨n, ?_⟩
      rw [← gcomp_rho_eq hN B g n, comp_rel]
      exact ⟨Y, hrho, hg⟩
    · rintro ⟨n, hn⟩
      rw [← gcomp_rho_eq hN B g n, comp_rel] at hn
      obtain ⟨Y, hrho, hg⟩ := hn
      exact ⟨Y, ⟨n, hrho⟩, hg⟩
  calc g.hom.1 = g.hom.1.comp (iSupRho hN) := by
        rw [iSupRho_eq_id hN]; exact (comp_idMap g.hom.1).symm
    _ = descMap hN B := hcomp

end Uniqueness

end Exercise619

end DomainTheory.NeighbourhoodSystems
