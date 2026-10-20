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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- The `X`-section of a two-variable map `g : 𝒟₀ × 𝒟₁ → 𝒟₂`: the map `𝒟₁ → 𝒟₂` with
`Y (gSection g X) Z ↔ X ∪ Y g Z`. -/
def gSection (g : ApproximableMap (prod V₀ V₁) V₂) {X : Set α} (hX : V₀.mem X) :
    ApproximableMap V₁ V₂ where
  rel Y Z := g.rel (prodNbhd X Y) Z
  rel_dom h := (prod_mem_prodNbhd_iff.mp (g.rel_dom h)).2
  rel_cod h := g.rel_cod h
  master_rel := g.rel_master (prod_mem_prodNbhd hX V₁.master_mem)
  inter_right h h' := g.inter_right h h'
  mono := by
    intro Y Y' Z Z' h hY'Y hZZ' hY' hZ'
    exact g.mono h (prodNbhd_subset_iff.mpr ⟨subset_rfl, hY'Y⟩) hZZ'
      (prod_mem_prodNbhd hX hY') hZ'

end DomainTheory.NeighbourhoodSystems
