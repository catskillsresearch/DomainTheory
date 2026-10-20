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

theorem lft_mem_Con_of_SumCon_rht_empty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (_hr : rhtFinset u = ∅) : lftFinset u ∈ A.Con := by
  rcases hu with ⟨hl, _⟩ | ⟨hl, _⟩
  · exact hl
  · rw [hl]; exact A.con_empty

end InfoSys

end DomainTheory.InformationSystems
