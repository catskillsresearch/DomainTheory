/-ai
An element x lies in the atom finset of a finite set of raw lambda tokens if and only if the atom token for x belongs to that set.

An auxiliary claim on multisets says that x lies in the right fold of atom insertion if and only if some member equals the atom of x. Both directions fail for the empty multiset. On a cons whose head is an atom, insertion membership splits into equality of that atom or existence in the tail. If the head is bottom or a function token, insertion acts as the identity, so a witness must come from the tail and the head cannot equal the atom. Applying the auxiliary claim to the underlying multiset and converting finset membership gives the stated equivalence.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

theorem mem_lamAtomFinset {u : Finset (RawLamToken α)} {x : α} :
    x ∈ lamAtomFinset u ↔ .atom x ∈ u := by
  have aux (s : Multiset (RawLamToken α)) :
      x ∈ Multiset.foldr lamAtomInsert (∅ : Finset α) s ↔ ∃ p ∈ s, p = .atom x := by
    refine Multiset.induction_on s ?_ ?_
    · constructor
      · intro hx; exact False.elim (Finset.notMem_empty x hx)
      · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
    · intro p t ih
      cases p with
      | atom a =>
        simp only [Multiset.foldr_cons, lamAtomInsert, Finset.mem_insert, ih, Multiset.mem_cons]
        constructor
        · rintro (hx | ⟨q, hq, hq'⟩)
          · exact ⟨.atom a, Or.inl rfl, congrArg RawLamToken.atom hx.symm⟩
          · exact ⟨q, Or.inr hq, hq'⟩
        · rintro ⟨q, hq, hq'⟩
          rcases hq with rfl | hq
          · injection hq' with hx; exact Or.inl hx.symm
          · exact Or.inr ⟨q, hq, hq'⟩
      | bot | funTok _ _ =>
        simp only [Multiset.foldr_cons, lamAtomInsert, id_eq, ih, Multiset.mem_cons]
        constructor
        · rintro ⟨q, hq, hq'⟩; exact ⟨q, Or.inr hq, hq'⟩
        · rintro ⟨q, hq, hq'⟩
          rcases hq with rfl | hq
          · exact False.elim (nomatch hq')
          · exact ⟨q, hq, hq'⟩
  constructor
  · intro hx
    rcases (aux u.1).1 hx with ⟨p, hp, hp'⟩
    subst hp'; exact Finset.mem_def.2 hp
  · intro hx
    exact (aux u.1).2 ⟨.atom x, Finset.mem_def.1 hx, rfl⟩

end InfoSys

end DomainTheory.InformationSystems
