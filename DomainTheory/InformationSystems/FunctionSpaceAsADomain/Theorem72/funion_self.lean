/-ai
Choice-free union of a finite set of tokens of the first carrier with itself equals that set.

Extensionality is used. Membership in the union is membership in either copy, hence in the set. Membership in the set is membership in the left copy of the union.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition62
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

theorem funion_self (u : Finset α) : u ∪' u = u := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h <;> exact h
  · intro hx
    exact mem_funion.mpr (Or.inl hx)

end InfoSys

end DomainTheory.InformationSystems
