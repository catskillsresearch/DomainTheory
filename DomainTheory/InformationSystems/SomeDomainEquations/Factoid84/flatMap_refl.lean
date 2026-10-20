module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

theorem flatMap_refl : ReflApprox flatMap := by
  intro u v ⟨_, _, hEnt⟩
  by_cases h1 : 1 ∈ u
  · exact Or.inl h1
  · refine Or.inr ⟨?_, ?_⟩
    · intro n hn; exact hEnt n hn
    · intro h1v
      have h := hEnt 1 h1v
      rcases h with h0 | h
      · exact absurd h0 (by decide)
      · exact h1 h

end Factoid84

end DomainTheory.InformationSystems
