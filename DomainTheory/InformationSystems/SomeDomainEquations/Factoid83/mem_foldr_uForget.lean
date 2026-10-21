/-ai
A V-token lies in the right fold of forget-insertion over a multiset of U-tokens, starting from the empty finset, if and only if some member has that value.

Induct on the multiset. The empty fold is empty, so neither side has a witness. On a cons, membership in the inserted fold is equality with the head value or membership in the tail fold. The inductive hypothesis turns the tail membership into existence in the tail, and reassembling the disjunction gives existence in the cons. The converse splits multiset membership in the same way.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst33
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.UToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.uForgetInsert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst39

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

theorem mem_foldr_uForget (s : Multiset UToken) (t : VToken) :
    t ∈ Multiset.foldr uForgetInsert ∅ s ↔ ∃ p ∈ s, p.val = t := by
  refine Multiset.induction_on s ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro p rest ih
    simp only [Multiset.foldr_cons, uForgetInsert, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (rfl | ⟨q, hq, hq'⟩)
      · exact ⟨p, Or.inl rfl, rfl⟩
      · exact ⟨q, Or.inr hq, hq'⟩
    · rintro ⟨q, hq, hq'⟩
      rcases hq with rfl | hq
      · exact Or.inl hq'.symm
      · exact Or.inr ⟨q, hq, hq'⟩

end InfoSys

end DomainTheory.InformationSystems
