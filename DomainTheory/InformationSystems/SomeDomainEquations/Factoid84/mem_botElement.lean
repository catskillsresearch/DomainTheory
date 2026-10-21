/-ai
A natural number belongs to the bottom element of the powerset system P if and only if it equals 0.

Membership in the closure of the empty set is entailment by the empty set. That entailment is equality with 0, because the empty set has no members. Conversely, equality with 0 is an entailment by the empty set.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.Basic

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35.mem_closure_iff
@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive
open InfoSys
open ApproximableMap

namespace Factoid84


theorem mem_botElement (x : ℕ) : x ∈ botElement.carrier ↔ x = 0 := by
  constructor
  · intro hx
    have : PEnt ∅ x := (P.mem_closure_iff (by trivial : (∅ : Finset ℕ) ∈ P.Con)).1 hx
    rcases this with rfl | hx'
    · rfl
    · exact False.elim (Finset.notMem_empty _ hx')
  · rintro rfl
    exact (P.mem_closure_iff (by trivial : (∅ : Finset ℕ) ∈ P.Con)).2 (Or.inl rfl)

end Factoid84
end DomainTheory.InformationSystems
