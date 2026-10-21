/-ai
An element belongs to the right projection of a finite set of sum tokens if and only if its right token belongs to the set.

Unfold the projection and rewrite by the membership lemma for the fold of right insertion. A witness token equal to the right token may be replaced by that right token, and the right token itself is a witness.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.mem_foldr_rht

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem mem_rhtFinset {u : Finset (SumToken α β)} {y : β} :
    y ∈ rhtFinset u ↔ SumToken.right y ∈ u := by
  unfold rhtFinset
  rw [mem_foldr_rht]
  constructor
  · rintro ⟨p, hp, hp'⟩
    rwa [← hp']
  · intro hy
    exact ⟨.right y, hy, rfl⟩

end InfoSys

end DomainTheory.InformationSystems
