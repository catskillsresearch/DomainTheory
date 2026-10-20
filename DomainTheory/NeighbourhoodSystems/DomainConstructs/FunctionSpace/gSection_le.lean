module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_master_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.toApproxMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_toFilter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_symm_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.leastMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.gSection
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.gSection_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

theorem gSection_le {g : ApproximableMap (prod V₀ V₁) V₂} {X X' : Set α}
    (hX : V₀.mem X) (hX' : V₀.mem X') (hX'X : X' ⊆ X) : gSection g hX ≤ gSection g hX' := by
  intro Y Z h
  have hY := (prod_mem_prodNbhd_iff.mp (g.rel_dom h)).2
  exact g.mono h (prodNbhd_subset_iff.mpr ⟨hX'X, subset_rfl⟩) subset_rfl
    (prod_mem_prodNbhd hX' hY) (g.rel_cod h)

end DomainTheory.NeighbourhoodSystems
