module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.atomFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.pairRFinset

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys


variable {α : Type*} [DecidableEq α]

theorem mem_foldr_atom (s : Multiset (TreeToken α)) (x : α) :
    x ∈ Multiset.foldr atomInsert (∅ : Finset α) s ↔ ∃ p ∈ s, p = .atom x := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro hx; exact False.elim (Finset.notMem_empty x hx)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p t ih
    cases p with
    | atom a =>
      simp only [Multiset.foldr_cons, atomInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (hx | ⟨q, hq, hq'⟩)
        · exact ⟨.atom a, Or.inl rfl, congrArg TreeToken.atom hx.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with hx; exact Or.inl hx.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | bot | pairL _ | pairR _ =>
      simp only [Multiset.foldr_cons, atomInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

end InfoSys

end DomainTheory.InformationSystems
