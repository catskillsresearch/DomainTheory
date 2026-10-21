/-ai
Left-pair insertion sends a left-pair token to insertion of its inner token and sends the bottom, an atom, and a right-pair token to the identity. That operation is left commutative, by casing on the two tokens and using commutativity of insertion when both are left-pair tokens, with the remaining cases definitionally equal. The left pair projection of a finite set of tree tokens is the fold of this insertion over the underlying multiset, starting from the empty set.

A tree token lies in such a fold if and only if the multiset contains the corresponding left-pair token. Consequently, a tree token lies in the left pair projection of a finite set if and only if the corresponding left-pair token lies in the set.

The fold claim is proved by induction on the multiset. The empty multiset has empty fold and contains no token. If the head is a left-pair token, membership in the inserted fold is equality with the inner token or membership in the fold of the tail, and the inductive hypothesis matches a witness in the tail with a witness in the cons, while a witness at the head is that left-pair token. If the head is the bottom, an atom, or a right-pair token, insertion acts as the identity, so membership is membership in the tail fold, and the head itself cannot be the desired left-pair token. The projection claim rewrites along this characterization: a witness equal to the left-pair token is an element of the finite set, and the left-pair token itself is such a witness.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.TreeToken

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false
universe u
variable {α : Type*} [DecidableEq α]
variable (A : InfoSys α)

private def pairLInsert : TreeToken α → Finset (TreeToken α) → Finset (TreeToken α)
  | .pairL t => insert t
  | .bot | .atom _ | .pairR _ => id

instance :
    LeftCommutative (pairLInsert : TreeToken α → Finset (TreeToken α) → Finset (TreeToken α)) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

def pairLFinset (u : Finset (TreeToken α)) : Finset (TreeToken α) :=
  Multiset.foldr pairLInsert (∅ : Finset (TreeToken α)) u.1

private theorem mem_foldr_pairL (s : Multiset (TreeToken α)) (t : TreeToken α) :
    t ∈ Multiset.foldr pairLInsert (∅ : Finset (TreeToken α)) s ↔
      ∃ p ∈ s, p = .pairL t := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p rest ih
    cases p with
    | pairL a =>
      simp only [Multiset.foldr_cons, pairLInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (ht | ⟨q, hq, hq'⟩)
        · exact ⟨.pairL a, Or.inl rfl, congrArg TreeToken.pairL ht.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with ht; exact Or.inl ht.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | bot | atom _ | pairR _ =>
      simp only [Multiset.foldr_cons, pairLInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

theorem mem_pairLFinset {u : Finset (TreeToken α)} {t : TreeToken α} :
    t ∈ pairLFinset u ↔ .pairL t ∈ u := by
  constructor
  · intro ht
    rcases (mem_foldr_pairL u.1 t).1 ht with ⟨p, hp, hp'⟩
    subst hp'; exact Finset.mem_def.2 hp
  · intro ht
    exact (mem_foldr_pairL u.1 t).2 ⟨.pairL t, Finset.mem_def.1 ht, rfl⟩

end InfoSys
end DomainTheory.InformationSystems
