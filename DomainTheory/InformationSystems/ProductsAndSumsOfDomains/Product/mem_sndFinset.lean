/-ai
A token y lies in the right projection of a finite set of product tokens if and only if some token of the set has least first component and second component y.

Unfolding the projection, the fold-membership lemma supplies a token of the filtered multiset whose second component is y. Membership in that filter is membership in the original set together with the least-first-component test, and the converse packages those data back into the filter.
ai-/
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst5
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst7
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeFstInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeSndInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.sndFinset
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.mem_foldr_snd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem mem_sndFinset {u : Finset (ProdToken A B)} {y : β} :
    y ∈ sndFinset A B u ↔ ∃ p ∈ u, p.val.1 = A.bot ∧ p.val.2 = y := by
  unfold sndFinset
  rw [mem_foldr_snd]
  constructor
  · rintro ⟨p, hp, hy⟩
    have hp' := Finset.mem_filter.mp hp
    exact ⟨p, hp'.1, hp'.2, hy⟩
  · rintro ⟨p, hp, hbot, hy⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hbot⟩, hy⟩

end InfoSys

end DomainTheory.InformationSystems
