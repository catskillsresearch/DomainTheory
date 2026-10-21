/-ai
The left projection of a finite set of tokens of the information system V is the set of payloads of the left-pair tokens in that set. It is the fold, starting from the empty set, of the operation that inserts the payload of a left-pair token and acts as the identity on the bottom token, the top token, and a right-pair token. That operation is left-commutative: the two tokens are compared, insertion commutes when both insert, and otherwise the two orders agree definitionally.

A token t belongs to the left projection of a finite set u if and only if the left-pair token with payload t belongs to u.

Membership in the fold is characterized by induction on the multiset. Both sides fail for the empty multiset. If the head is a left-pair token, membership after insertion is equality with the payload or membership in the tail, matching a witness that is the head or lies in the tail. If the head is the bottom token, the top token, or a right-pair token, the fold is unchanged and that head cannot be the witness, so membership reduces to the tail.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

private def pairLInsert : VToken → Finset VToken → Finset VToken
  | .pairL t => insert t
  | .bot | .top | .pairR _ => id

instance :
    LeftCommutative (pairLInsert : VToken → Finset VToken → Finset VToken) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

/-- Left projection: `{X | (X, Δ) ∈ u}`. -/
def vPairLFinset (u : Finset VToken) : Finset VToken :=
  Multiset.foldr pairLInsert (∅ : Finset VToken) u.1

private theorem mem_foldr_pairL (s : Multiset VToken) (t : VToken) :
    t ∈ Multiset.foldr pairLInsert (∅ : Finset VToken) s ↔
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
        · exact ⟨.pairL a, Or.inl rfl, congrArg VToken.pairL ht.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with ht; exact Or.inl ht.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | bot | top | pairR _ =>
      simp only [Multiset.foldr_cons, pairLInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

theorem mem_vPairLFinset {u : Finset VToken} {t : VToken} :
    t ∈ vPairLFinset u ↔ .pairL t ∈ u := by
  simpa [vPairLFinset] using mem_foldr_pairL u.1 t

end InfoSys
end DomainTheory.InformationSystems
