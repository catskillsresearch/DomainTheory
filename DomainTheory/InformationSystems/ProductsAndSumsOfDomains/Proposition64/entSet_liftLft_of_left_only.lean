module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.Basic
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.SumCon_liftSumLeft

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

variable {C : InfoSys γ}


theorem entSet_liftLft_of_left_only {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hr : rhtFinset u = ∅) :
    (sumSystem A B).EntSet (liftSumLeft (β := β) (lftFinset u)) u := by
  intro p hp
  cases p with
  | bot =>
    exact ⟨SumCon_liftSumLeft A B (lft_mem_Con_of_SumCon_rht_empty A B hu hr), trivial⟩
  | left x =>
    have hx : x ∈ lftFinset u := (mem_lftFinset).2 hp
    refine ⟨SumCon_liftSumLeft A B (lft_mem_Con_of_SumCon_rht_empty A B hu hr), ⟨?_, ?_⟩⟩
    · rw [lftFinset_liftSumLeft]; exact Finset.ne_empty_of_mem hx
    · rw [lftFinset_liftSumLeft]
      exact A.ent_refl (lft_mem_Con_of_SumCon_rht_empty A B hu hr) hx
  | right y =>
    exact False.elim (by
      have : y ∈ rhtFinset u := (mem_rhtFinset).2 hp
      rw [hr] at this
      exact Finset.notMem_empty _ this)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
