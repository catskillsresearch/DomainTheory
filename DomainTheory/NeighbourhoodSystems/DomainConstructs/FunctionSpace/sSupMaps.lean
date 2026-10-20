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
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.PointwiseBounded
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.supOnPrincipal
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace.supOnPrincipal_mono

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Theorem 3.13(iii) (Scott 1981, PRG-19).** The least upper bound of a pointwise-bounded set
`F`, defined on principal inputs by `supOnPrincipal` and extended via Exercise 2.8 (`ofMono`). -/
def sSupMaps (F : Set (ApproximableMap V₀ V₁)) (hF : PointwiseBounded F) : ApproximableMap V₀ V₁ :=
  ofMono (fun X hX => supOnPrincipal F hF X hX) (supOnPrincipal_mono F hF)

end DomainTheory.NeighbourhoodSystems
