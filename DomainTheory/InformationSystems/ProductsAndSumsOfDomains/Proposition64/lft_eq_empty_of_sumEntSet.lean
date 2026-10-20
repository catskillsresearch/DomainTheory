module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumRight

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false

theorem lft_eq_empty_of_sumEntSet {u u' : Finset (SumToken α β)}
    (hl : lftFinset u = ∅) (hEnt : (sumSystem A B).EntSet u u') :
    lftFinset u' = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim ((hEnt _ ((mem_lftFinset).1 hx)).2.1 hl)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

end InfoSys

end DomainTheory.InformationSystems
