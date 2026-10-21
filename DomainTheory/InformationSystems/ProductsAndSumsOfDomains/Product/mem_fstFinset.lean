/-ai
A token x lies in the left projection of a finite set of product tokens if and only if some token of the set has least second component and first component x.

Unfolding the projection, the fold-membership lemma supplies a token of the filtered multiset whose first component is x. Membership in that filter is membership in the original set together with the least-second-component test, and the converse packages those data back into the filter.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst5
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst7
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeFstInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeSndInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.fstFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.mem_foldr_fst

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem mem_fstFinset {u : Finset (ProdToken A B)} {x : α} :
    x ∈ fstFinset A B u ↔ ∃ p ∈ u, p.val.2 = B.bot ∧ p.val.1 = x := by
  unfold fstFinset
  rw [mem_foldr_fst]
  constructor
  · rintro ⟨p, hp, hx⟩
    have hp' := Finset.mem_filter.mp hp
    exact ⟨p, hp'.1, hp'.2, hx⟩
  · rintro ⟨p, hp, hbot, hx⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hbot⟩, hx⟩

end InfoSys

end DomainTheory.InformationSystems
