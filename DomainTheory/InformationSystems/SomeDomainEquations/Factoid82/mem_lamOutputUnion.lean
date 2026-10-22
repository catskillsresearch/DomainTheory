/-ai
A raw token lies in the output union of a finite set of list pairs if and only if it lies in the finite set of the second list of some pair in the set.

An auxiliary claim on multisets says that the token lies in the right fold of output-union insertion if and only if it lies in the second-list finset of some member. Both directions fail for the empty multiset. On a cons, membership in the choice-free union of the head's second-list finset with the tail fold splits into those two alternatives, matching existence in the cons. Simplifying the definition of output union reduces the claim to this auxiliary statement on the underlying multiset.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.listToFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst10
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamOutUnionInsert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst17
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst18
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamOutputUnion

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem mem_lamOutputUnion {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    {t : RawLamToken α} :
    t ∈ lamOutputUnion s ↔ ∃ p ∈ s, t ∈ listToFinset p.2 := by
  have aux (m : Multiset (List (RawLamToken α) × List (RawLamToken α))) :
      t ∈ Multiset.foldr (lamOutUnionInsert (α := α)) ∅ m ↔
        ∃ p ∈ m, t ∈ listToFinset p.2 := by
    refine Multiset.induction_on m ?_ ?_
    · constructor
      · intro ht; exact False.elim (Finset.notMem_empty t ht)
      · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
    · intro p rest ih
      simp only [Multiset.foldr_cons, lamOutUnionInsert, mem_funion, ih, Multiset.mem_cons]
      constructor
      · rintro (ht | ⟨q, hq, ht⟩)
        · exact ⟨p, Or.inl rfl, ht⟩
        · exact ⟨q, Or.inr hq, ht⟩
      · rintro ⟨q, hq, ht⟩
        rcases hq with rfl | hq
        · exact Or.inl ht
        · exact Or.inr ⟨q, hq, ht⟩
  simpa [lamOutputUnion] using aux s.1

end InfoSys

end DomainTheory.InformationSystems
