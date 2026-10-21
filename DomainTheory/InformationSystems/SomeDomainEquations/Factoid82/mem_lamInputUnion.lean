/-ai
A raw token lies in the input union of a finite set of list pairs if and only if it lies in the finite set of the first list of some pair in the set.

An auxiliary claim on multisets says that the token lies in the right fold of input-union insertion if and only if it lies in the first-list finset of some member. Both directions fail for the empty multiset. On a cons, membership in the choice-free union of the head's first-list finset with the tail fold splits into those two alternatives, matching existence in the cons. Simplifying the definition of input union reduces the claim to this auxiliary statement on the underlying multiset.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.listToFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst10
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamInUnionInsert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst17
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst18
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamInputUnion

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem mem_lamInputUnion {s : Finset (List (RawLamToken α) × List (RawLamToken α))}
    {t : RawLamToken α} :
    t ∈ lamInputUnion s ↔ ∃ p ∈ s, t ∈ listToFinset p.1 := by
  have aux (m : Multiset (List (RawLamToken α) × List (RawLamToken α))) :
      t ∈ Multiset.foldr (lamInUnionInsert (α := α)) ∅ m ↔
        ∃ p ∈ m, t ∈ listToFinset p.1 := by
    refine Multiset.induction_on m ?_ ?_
    · constructor
      · intro ht; exact False.elim (Finset.notMem_empty t ht)
      · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
    · intro p rest ih
      simp only [Multiset.foldr_cons, lamInUnionInsert, mem_funion, ih, Multiset.mem_cons]
      constructor
      · rintro (ht | ⟨q, hq, ht⟩)
        · exact ⟨p, Or.inl rfl, ht⟩
        · exact ⟨q, Or.inr hq, ht⟩
      · rintro ⟨q, hq, ht⟩
        rcases hq with rfl | hq
        · exact Or.inl ht
        · exact Or.inr ⟨q, hq, ht⟩
  simpa [lamInputUnion] using aux s.1

end InfoSys

end DomainTheory.InformationSystems
