module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.BasicInst3
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_step
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_stepFun
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.stepFun_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.step_master_eq
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpace_master
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.toApproxMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.mem_toFilter
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.funSpaceEquiv_symm_apply
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.interYs_nil
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.leastMap_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.gSection_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curry
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.curry_rel
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.rel_stepFun_iff
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.uncurry
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.uncurry_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable {V₂ : NeighborhoodSystem γ}

/-- **Theorem 3.12 (Scott 1981, PRG-19).** `curry (uncurry h) = h`. -/
theorem curry_uncurry (h : ApproximableMap V₀ (funSpace V₁ V₂)) : curry (uncurry h) = h := by
  apply ApproximableMap.ext
  intro X W
  constructor
  · rintro ⟨hX, hW, hmem⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
    refine (rel_stepFun_iff h hX hL).mpr (fun p hp => ?_)
    have := hmem p hp
    -- `gSection (uncurry h) hX ∈ step p.1 p.2` means `(uncurry h).rel (prodNbhd X p.1) p.2`
    have hrel : (uncurry h).rel (prodNbhd X p.1) p.2 := this
    obtain ⟨_, hrel'⟩ := hrel
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd] at hrel'
    exact hrel'
  · intro hrel
    have hX : V₀.mem X := h.rel_dom hrel
    have hW : (funSpace V₁ V₂).mem W := h.rel_cod hrel
    refine ⟨hX, hW, ?_⟩
    obtain ⟨⟨L, hL, rfl⟩, _⟩ := hW
    intro p hp
    show (uncurry h).rel (prodNbhd X p.1) p.2
    refine ⟨prod_mem_prodNbhd hX (hL p hp).1, ?_⟩
    rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
    exact (rel_stepFun_iff h hX hL).mp hrel p hp

end DomainTheory.NeighbourhoodSystems
