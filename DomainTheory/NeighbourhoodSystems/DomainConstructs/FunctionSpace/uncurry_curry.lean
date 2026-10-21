/-ai
Theorem 3.12 of Scott (1981, PRG-19) states that uncurrying the curry of an approximable map g recovers g.

The two maps have the same relation. If the uncurried curry relates a neighbourhood W to an output, the product-neighbourhood preimage identity rewrites that relation as the relation of g. Conversely, the domain of the relation of g is a product neighbourhood whose left and right slices are neighbourhoods, and the relation of g on the product of those preimages is the original relation by the same identity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_master_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.toApproxMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_toFilter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_symm_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.leastMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.gSection_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curry
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curry_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.prod_mem_inl
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.prod_mem_inr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.uncurry
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.uncurry_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `uncurry (curry g) = g`. -/
theorem uncurry_curry (g : ApproximableMap (prod V₀ V₁) V₂) : uncurry (curry g) = g := by
  apply ApproximableMap.ext
  intro W Z
  constructor
  · rintro ⟨hW, _, _, hmem⟩
    rw [prodNbhd_preimage hW]; exact hmem
  · intro hrel
    have hW := g.rel_dom hrel
    refine ⟨hW, prod_mem_inl hW, step_mem (prod_mem_inr hW) (g.rel_cod hrel), ?_⟩
    show g.rel (prodNbhd (Sum.inl ⁻¹' W) (Sum.inr ⁻¹' W)) Z
    rwa [← prodNbhd_preimage hW]

end DomainTheory.NeighbourhoodSystems
