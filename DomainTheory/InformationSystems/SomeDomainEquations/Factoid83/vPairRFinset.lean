/-ai
The right projection of a finite set of tokens of the information system V is the set of payloads of the right-pair tokens in that set. It is the fold, starting from the empty set, of the operation that inserts the payload of a right-pair token and acts as the identity on the bottom token, the top token, and a left-pair token. That operation is left-commutative: the two tokens are compared, insertion commutes when both insert, and otherwise the two orders agree definitionally.

A token t belongs to the right projection of a finite set u if and only if the right-pair token with payload t belongs to u.

Membership in the fold is characterized by induction on the multiset. Both sides fail for the empty multiset. If the head is a right-pair token, membership after insertion is equality with the payload or membership in the tail, matching a witness that is the head or lies in the tail. If the head is the bottom token, the top token, or a left-pair token, the fold is unchanged and that head cannot be the witness, so membership reduces to the tail.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

private def pairRInsert : VToken → Finset VToken → Finset VToken
  | .pairR t => insert t
  | .bot | .top | .pairL _ => id

instance :
    LeftCommutative (pairRInsert : VToken → Finset VToken → Finset VToken) :=
  ⟨fun p q s => by cases p <;> cases q <;> first | exact insert_comm' _ _ s | rfl⟩

/-- Right projection: `{Y | (Δ, Y) ∈ u}`. -/
def vPairRFinset (u : Finset VToken) : Finset VToken :=
  Multiset.foldr pairRInsert (∅ : Finset VToken) u.1

private theorem mem_foldr_pairR (s : Multiset VToken) (t : VToken) :
    t ∈ Multiset.foldr pairRInsert (∅ : Finset VToken) s ↔
      ∃ p ∈ s, p = .pairR t := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p rest ih
    cases p with
    | pairR a =>
      simp only [Multiset.foldr_cons, pairRInsert, Finset.mem_insert, ih, Multiset.mem_cons]
      constructor
      · rintro (ht | ⟨q, hq, hq'⟩)
        · exact ⟨.pairR a, Or.inl rfl, congrArg VToken.pairR ht.symm⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · injection hq' with ht; exact Or.inl ht.symm
        · exact Or.inr ⟨q, hq, hq'⟩
    | bot | top | pairL _ =>
      simp only [Multiset.foldr_cons, pairRInsert, id_eq, ih, Multiset.mem_cons]
      constructor
      · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, hq, hq'⟩
        rcases hq with rfl | hq
        · exact False.elim (nomatch hq')
        · exact ⟨q, hq, hq'⟩

theorem mem_vPairRFinset {u : Finset VToken} {t : VToken} :
    t ∈ vPairRFinset u ↔ .pairR t ∈ u := by
  simpa [vPairRFinset] using mem_foldr_pairR u.1 t

end InfoSys
end DomainTheory.InformationSystems
