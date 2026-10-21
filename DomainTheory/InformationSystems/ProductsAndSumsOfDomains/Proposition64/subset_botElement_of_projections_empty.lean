/-ai
A finite set of sum tokens whose left and right projections are both empty is contained in the bottom element of the separated sum.

A member of the set is the sum bottom, which belongs to the bottom element by reflexivity of entailment on its singleton, or a left or right token, each of which would lie in the corresponding projection.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap

variable {C : InfoSys γ}


theorem subset_botElement_of_projections_empty {u : Finset (SumToken α β)}
    (hl : lftFinset u = ∅) (hr : rhtFinset u = ∅) :
    (↑u : Set (SumToken α β)) ⊆ (sumSystem A B).botElement.carrier := by
  intro p hp
  have hp' : p ∈ u := Finset.mem_coe.1 hp
  cases p with
  | bot =>
    exact (sumSystem A B).ent_refl ((sumSystem A B).con_sing _) (Finset.mem_singleton_self _)
  | left x =>
    exact False.elim (by
      have : x ∈ lftFinset u := (mem_lftFinset).2 hp'
      rw [hl] at this; exact Finset.notMem_empty _ this)
  | right y =>
    exact False.elim (by
      have : y ∈ rhtFinset u := (mem_rhtFinset).2 hp'
      rw [hr] at this; exact Finset.notMem_empty _ this)

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
