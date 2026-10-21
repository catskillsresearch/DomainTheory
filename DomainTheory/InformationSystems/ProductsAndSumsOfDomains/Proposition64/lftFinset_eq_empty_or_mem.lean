/-ai
The left projection of a finite set of sum tokens is empty, or else it contains some token. The argument avoids a decision procedure for equality of finite sets.

Induction on the finite set. The empty set has empty left projection. Inserting a left token puts that token into the left projection. Inserting a right token or the sum bottom leaves the left projection unchanged, so the inductive alternative applies.
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

set_option linter.unusedSectionVars false



















namespace ApproximableMap

variable {C : InfoSys γ}









/-- Choice-free emptiness dichotomy for `lftFinset` (avoids `Finset.decidableEq`). -/
theorem lftFinset_eq_empty_or_mem (u : Finset (SumToken α β)) :
    lftFinset u = ∅ ∨ ∃ x, x ∈ lftFinset u := by
  induction u using Finset.induction_on with
  | empty =>
    exact Or.inl lftFinset_empty
  | insert p s _hp ih =>
    cases p with
    | left x =>
      exact Or.inr ⟨x, by rw [lftFinset_insert_left]; exact Finset.mem_insert_self _ _⟩
    | right y =>
      rw [lftFinset_insert_right]; exact ih
    | bot =>
      rw [lftFinset_insert_bot]; exact ih

end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
