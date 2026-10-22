module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.SumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instDecidableEqSumToken
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.rhtInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeLftInsert
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.instLeftCommutativeRhtInsert

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

omit [DecidableEq α] in

theorem mem_foldr_rht (s : Multiset (SumToken α β)) (y : β) :
    y ∈ Multiset.foldr rhtInsert (∅ : Finset β) s ↔ ∃ p ∈ s, p = .right y := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hy
      exact False.elim (Finset.notMem_empty y hy)
    · rintro ⟨_, hp, _⟩
      exact False.elim (by cases hp)
  · intro p t ih
    cases p with
    | right b =>
      simp only [Multiset.foldr_cons, rhtInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (hy | ⟨q, hq, hq'⟩)
        · exact ⟨.right b, Or.inl rfl, congrArg SumToken.right hy.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with hy
          exact Or.inl hy.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | left a =>
      simp only [Multiset.foldr_cons, rhtInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩
        exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩
    | bot =>
      simp only [Multiset.foldr_cons, rhtInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩
        exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

end InfoSys

end DomainTheory.InformationSystems
