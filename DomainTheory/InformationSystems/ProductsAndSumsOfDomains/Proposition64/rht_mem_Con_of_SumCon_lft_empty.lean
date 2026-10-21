/-ai
If a finite set u of sum tokens is sum-consistent and its left projection is empty, then the right projection of u is consistent in B.

Case analysis on sum consistency. The left disjunct rewrites the right projection to the empty set, which is consistent in B. The right disjunct states that the right projection is consistent.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumLeft
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.instLeftCommutativeLiftSumRight

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β)

theorem rht_mem_Con_of_SumCon_lft_empty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (_hl : lftFinset u = ∅) : rhtFinset u ∈ B.Con := by
  rcases hu with ⟨_, hr⟩ | ⟨_, hr⟩
  · rw [hr]; exact B.con_empty
  · exact hr

end InfoSys

end DomainTheory.InformationSystems
