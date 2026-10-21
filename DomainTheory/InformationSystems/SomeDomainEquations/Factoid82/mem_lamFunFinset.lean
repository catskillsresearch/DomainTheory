/-ai
A pair of raw-token lists lies in the function finset of a finite set of raw lambda tokens if and only if the function token of those two lists belongs to the set.

An auxiliary claim on multisets says that the pair lies in the right fold of function insertion if and only if some member equals that function token. Both directions fail for the empty multiset. On a cons whose head is a function token, insertion membership splits into equality of the pair or existence in the tail. If the head is bottom or an atom, insertion acts as the identity, so a witness must come from the tail and the head cannot equal the function token. Applying the auxiliary claim to the underlying multiset and converting finset membership gives the stated equivalence.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunInsert
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst9
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepthInst10
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamFunFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem mem_lamFunFinset {u : Finset (RawLamToken α)}
    {p : List (RawLamToken α) × List (RawLamToken α)} :
    p ∈ lamFunFinset u ↔ .funTok p.1 p.2 ∈ u := by
  have aux (s : Multiset (RawLamToken α)) :
      p ∈ Multiset.foldr lamFunInsert ∅ s ↔ ∃ t ∈ s, t = .funTok p.1 p.2 := by
    refine Multiset.induction_on s ?_ ?_
    · constructor
      · intro hp; exact False.elim (Finset.notMem_empty p hp)
      · rintro ⟨_, ht, _⟩; exact False.elim (by cases ht)
    · intro t rest ih
      cases t with
      | funTok u v =>
        simp only [Multiset.foldr_cons, lamFunInsert, Finset.mem_insert, ih, Multiset.mem_cons]
        constructor
        · rintro (hp | ⟨q, hq, hq'⟩)
          · exact ⟨.funTok u v, Or.inl rfl, by cases hp; rfl⟩
          · exact ⟨q, Or.inr hq, hq'⟩
        · rintro ⟨q, hq, hq'⟩
          rcases hq with rfl | hq
          · injection hq' with hu hv
            exact Or.inl (Prod.ext hu.symm hv.symm)
          · exact Or.inr ⟨q, hq, hq'⟩
      | bot | atom _ =>
        simp only [Multiset.foldr_cons, lamFunInsert, id_eq, ih, Multiset.mem_cons]
        constructor
        · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
        · rintro ⟨q, hq, hq'⟩
          rcases hq with rfl | hq
          · exact False.elim (nomatch hq')
          · exact ⟨q, hq, hq'⟩
  constructor
  · intro hp
    rcases (aux u.1).1 hp with ⟨t, ht, ht'⟩
    subst ht'; exact Finset.mem_def.2 ht
  · intro hp
    exact (aux u.1).2 ⟨.funTok p.1 p.2, Finset.mem_def.1 hp, rfl⟩

end InfoSys

end DomainTheory.InformationSystems
