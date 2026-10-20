module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.Ypd_eq_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.subCode_computable

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- **Scott's relation (i) for `ℙ𝒟`, at the level of codes:** equality of two enumerated
neighbourhoods is recursively decidable. -/
theorem eqCode_computable : RecDecidable₂ (fun c k => V.Ypd P c = V.Ypd P k) := by
  have h := (V.subCode_computable P).and (V.subCode_computable P).swap
  refine RecDecidable.of_iff (fun t => ?_) h
  exact V.Ypd_eq_iff P

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
