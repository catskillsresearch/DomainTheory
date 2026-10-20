module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.SumCon_liftSumRight

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

set_option linter.unusedSectionVars false



















namespace ApproximableMap

variable {C : InfoSys γ}









theorem entSet_liftRht_of_right_only {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hl : lftFinset u = ∅) :
    (sumSystem A B).EntSet (liftSumRight (α := α) (rhtFinset u)) u := by
  intro p hp
  cases p with
  | bot =>
    exact ⟨SumCon_liftSumRight A B (rht_mem_Con_of_SumCon_lft_empty A B hu hl), trivial⟩
  | right y =>
    have hy : y ∈ rhtFinset u := (mem_rhtFinset).2 hp
    refine ⟨SumCon_liftSumRight A B (rht_mem_Con_of_SumCon_lft_empty A B hu hl), ⟨?_, ?_⟩⟩
    · rw [rhtFinset_liftSumRight]; exact Finset.ne_empty_of_mem hy
    · rw [rhtFinset_liftSumRight]
      exact B.ent_refl (rht_mem_Con_of_SumCon_lft_empty A B hu hl) hy
  | left x =>
    exact False.elim (by
      have : x ∈ lftFinset u := (mem_lftFinset).2 hp
      rw [hl] at this
      exact Finset.notMem_empty _ this)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
