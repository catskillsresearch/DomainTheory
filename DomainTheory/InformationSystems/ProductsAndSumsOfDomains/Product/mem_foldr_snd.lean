module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst5
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst7
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeFstInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeSndInsert

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem mem_foldr_snd (s : Multiset (ProdToken A B)) (y : β) :
    y ∈ Multiset.foldr (fun p : ProdToken A B => insert p.val.2) (∅ : Finset β) s ↔
      ∃ p ∈ s, p.val.2 = y := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hy
      exact False.elim (Finset.notMem_empty y hy)
    · rintro ⟨p, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hy | ⟨q, hq, hq2⟩)
      · exact ⟨p, Or.inl rfl, hy.symm⟩
      · exact ⟨q, Or.inr hq, hq2⟩
    · rintro ⟨q, hq, hq2⟩
      rcases hq with rfl | hq
      · exact Or.inl hq2.symm
      · exact Or.inr ⟨q, hq, hq2⟩

end InfoSys

end DomainTheory.InformationSystems
