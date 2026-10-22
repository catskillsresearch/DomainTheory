module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.liftSumRight
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.mem_foldr_liftSumRight

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

theorem mem_liftSumRight {w : Finset β} {p : SumToken α β} :
    p ∈ liftSumRight (α := α) w ↔ ∃ y ∈ w, p = .right y := by
  simpa [liftSumRight] using mem_foldr_liftSumRight (α := α) w.1 p

end InfoSys

end DomainTheory.InformationSystems
