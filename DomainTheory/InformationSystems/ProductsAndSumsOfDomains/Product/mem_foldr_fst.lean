module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst5
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.ProdToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.BasicInst7
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeFstInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.instLeftCommutativeSndInsert

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

theorem mem_foldr_fst (s : Multiset (ProdToken A B)) (x : α) :
    x ∈ Multiset.foldr (fun p : ProdToken A B => insert p.val.1) (∅ : Finset α) s ↔
      ∃ p ∈ s, p.val.1 = x := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hx
      exact False.elim (Finset.notMem_empty x hx)
    · rintro ⟨p, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    simp only [Multiset.foldr_cons, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (hx | ⟨q, hq, hq1⟩)
      · exact ⟨p, Or.inl rfl, hx.symm⟩
      · exact ⟨q, Or.inr hq, hq1⟩
    · rintro ⟨q, hq, hq1⟩
      rcases hq with rfl | hq
      · exact Or.inl hq1.symm
      · exact Or.inr ⟨q, hq, hq1⟩

end InfoSys

end DomainTheory.InformationSystems
