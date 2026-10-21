/-ai
If a sum-consistent finite set has nonempty right projection, then its left projection is empty.

The left disjunct of sum consistency says that the right projection is empty, which contradicts the hypothesis. The right disjunct says that the left projection is empty.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.lftFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumCon

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem SumCon_lft_empty_of_rht_nonempty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hne : rhtFinset u ≠ ∅) : lftFinset u = ∅ := by
  rcases hu with ⟨_, hr⟩ | ⟨hl, _⟩
  · exact False.elim (hne hr)
  · exact hl

end InfoSys

end DomainTheory.InformationSystems
