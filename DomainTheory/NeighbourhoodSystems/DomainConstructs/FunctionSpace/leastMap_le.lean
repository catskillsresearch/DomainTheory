module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.toApproxMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.toFilter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.leastMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.MapsBounded
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.PointwiseBounded
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.supOnPrincipal
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.sSupMaps
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.eval
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.evalMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.gSection
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curry
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.uncurry
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curryEquiv
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_cons
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_append
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_singleton
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_master_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_inter_right
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_subset
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_mem_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_mem
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.toApproxMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_toFilter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_symm_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_mem_inter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_up_closed
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_mem_up_closed
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_cons
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_interYs
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_subset_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_antitone
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.leastMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mapsBounded_principal
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.supOnPrincipal_mono
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.gSection_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.gSection_le
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curry_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.rel_stepFun_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.prod_mem_inl
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.prod_mem_inr
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.uncurry_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.uncurry_curry
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curry_uncurry
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.rel_interYs

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Proposition 3.9 (Scott 1981, PRG-19).** `f₀` is the *minimal* element of the neighbourhood:
any `f` with `Xᵢ f Yᵢ` for all `i` satisfies `f₀ ⊆ f`. -/
theorem leastMap_le {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {f : ApproximableMap V₀ V₁}
    (hf : f ∈ stepFun L) : leastMap L hL hcons ≤ f := by
  rintro X Y ⟨hX, hY, hsub⟩
  exact f.mono (rel_interYs hf hX) subset_rfl hsub hX hY

end DomainTheory.NeighbourhoodSystems
