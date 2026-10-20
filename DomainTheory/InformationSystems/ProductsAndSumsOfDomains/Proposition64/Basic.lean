module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.liftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.inlMap
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.inrMap
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.copairMap
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.sumLftCarrier
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.sumRhtCarrier
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.sumElementLft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.sumElementRht
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.mem_foldr_liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.mem_foldr_liftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.mem_liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.mem_liftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.lftFinset_liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.rhtFinset_liftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.rhtFinset_liftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.lftFinset_liftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.rht_eq_empty_of_sumEntSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.lft_eq_empty_of_sumEntSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.entSet_lft_of_sumEntSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.entSet_rht_of_sumEntSet
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.lft_mem_Con_of_SumCon_rht_empty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.rht_mem_Con_of_SumCon_lft_empty
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.copair_union_disj

@[expose] public section

/-!
# Proposition 6.4 — sum injections and copairing

**Scott 1982, Proposition 6.4.** Approximable `inl`, `inr`, and unique copairing
`[f, g]` with `[f, g] ∘ inl = f`, `[f, g] ∘ inr = g`, and `[f, g](⊥) = ⊥`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false



















namespace ApproximableMap

variable {C : InfoSys γ}








end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
