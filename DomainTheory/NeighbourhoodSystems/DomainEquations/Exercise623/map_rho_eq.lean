/-ai
The expression functor applied to the n-th projection equals the injection of the image subsystem composed with its projection. The image is the subsystem obtained by applying the functor to the n-th level inside the syntactic domain.

Unfold the projection as the injection of the level composed with its projection. The functor preserves this composite because the injection is strict, and it carries the injection and the projection to those of the image subsystem.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gGen_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gTower_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.mem_gColim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gColim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Texp
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.BasicInst28
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.id_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.comp_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctor_obj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.gFunctorMap_val
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.descRel_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.inj_isStrict
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.map_inj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.map_proj
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.expSub
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.rho

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {A₀ A₁ B₀ B₁ : ScottSys}

section Uniqueness

variable {N : ScottSys} (hN : ([] : Str) ∈ N.sys.master)

/-- `T(ρₙ) = T(iₙ) ∘ T(jₙ) = i'ₙ ∘ j'ₙ`, the projection pair of `T(Texpⁿ{Γ}) ◁ T(Exp)`. -/
theorem map_rho_eq (n : ℕ) :
    (Texp N).map (rho hN n)
      = ((Texp N).obj_subsystem (expSub hN n)).inj.comp
        ((Texp N).obj_subsystem (expSub hN n)).proj := by
  unfold rho
  rw [(Texp N).map_comp (expSub hN n).proj (Subsystem.inj_isStrict (expSub hN n)),
      (Texp N).map_inj, (Texp N).map_proj]

end Uniqueness

end Exercise619

end DomainTheory.NeighbourhoodSystems
