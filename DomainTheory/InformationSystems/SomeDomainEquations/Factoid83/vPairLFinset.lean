module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
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

theorem vPairLFinset.insert_top (u : Finset VToken) :
    vPairLFinset (insert (.top : VToken) u) = vPairLFinset u := by
  ext t; simp only [mem_vPairLFinset, Finset.mem_insert]
  constructor
  · rintro (h | h); exacts [False.elim (nomatch h), h]
  · exact Or.inr

end InfoSys


end DomainTheory.InformationSystems
