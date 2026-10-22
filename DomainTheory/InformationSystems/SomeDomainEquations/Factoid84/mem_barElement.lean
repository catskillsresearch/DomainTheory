module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35.mem_closure_iff
@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

theorem mem_barElement (n x : ℕ) :
    x ∈ (barElement n).carrier ↔ x = 0 ∨ x = n := by
  constructor
  · intro hx
    have : PEnt (bar n) x := (P.mem_closure_iff (by trivial : bar n ∈ P.Con)).1 hx
    rcases this with rfl | hx'
    · exact Or.inl rfl
    · exact Or.inr (Finset.mem_singleton.mp hx')
  · intro h
    rcases h with rfl | hn
    · exact (P.mem_closure_iff (by trivial : bar n ∈ P.Con)).2 (Or.inl rfl)
    · rw [hn]
      exact (P.mem_closure_iff (by trivial : bar n ∈ P.Con)).2
        (Or.inr (Finset.mem_singleton_self n))

end Factoid84

end DomainTheory.InformationSystems
