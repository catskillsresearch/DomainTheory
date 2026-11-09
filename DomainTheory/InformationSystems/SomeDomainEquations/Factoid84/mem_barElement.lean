module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.comp
public import DomainTheory.InformationSystems.ElementsOfASystem.topElement
public import DomainTheory.InformationSystems.ElementsOfASystem.closure
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox

public import DomainTheory.InformationSystems.ElementsOfASystem.closure
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
    have : PEnt (bar n) x := (closure.mem_iff P (by trivial : bar n ∈ P.Con)).1 hx
    rcases this with rfl | hx'
    · exact Or.inl rfl
    · exact Or.inr (Finset.mem_singleton.mp hx')
  · intro h
    rcases h with rfl | hn
    · exact (closure.mem_iff P (by trivial : bar n ∈ P.Con)).2 (Or.inl rfl)
    · rw [hn]
      exact (closure.mem_iff P (by trivial : bar n ∈ P.Con)).2
        (Or.inr (Finset.mem_singleton_self n))

end Factoid84

end DomainTheory.InformationSystems
