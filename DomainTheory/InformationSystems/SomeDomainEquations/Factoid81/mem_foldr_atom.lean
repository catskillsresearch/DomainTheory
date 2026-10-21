/-ai
An atom lies in the fold of atom insertion over a multiset of tree tokens, starting from the empty set, if and only if that multiset contains the corresponding atom token.

Induct on the multiset. The empty multiset has empty fold and contains no token. If the head is an atom token, membership in the inserted fold is equality with the inserted atom or membership in the fold of the tail, and the inductive hypothesis matches a witness in the tail with a witness in the cons, while a witness at the head is that atom token. If the head is the bottom or a pair constructor, atom insertion acts as the identity, so membership is membership in the tail fold; a witness in the tail remains a witness in the cons, and the head itself cannot be the desired atom token.
ai-/
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

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

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
