/-ai
If a sum-consistent finite set has nonempty left projection, then its right projection is empty.

The left disjunct of sum consistency says that the right projection is empty. The right disjunct says that the left projection is empty, which contradicts the hypothesis.
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

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem SumCon_rht_empty_of_lft_nonempty {u : Finset (SumToken α β)}
    (hu : SumCon A B u) (hne : lftFinset u ≠ ∅) : rhtFinset u = ∅ := by
  rcases hu with ⟨_, hr⟩ | ⟨hl, _⟩
  · exact hr
  · exact False.elim (hne hl)

end InfoSys

end DomainTheory.InformationSystems
