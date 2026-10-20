module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.mem_topElement
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

theorem flatMap_toElement_of_mem_one {x : P.Element} (h1 : 1 ∈ x.carrier) :
    flatMap.toElement x = topElement := by
  apply le_antisymm
  · intro _ _; exact mem_topElement _
  · intro n _
    refine ⟨{1}, ?_, Or.inl (Finset.mem_singleton_self 1)⟩
    intro a ha
    have : a = 1 := Finset.mem_singleton.mp (Finset.mem_coe.1 ha)
    subst this; exact h1

end Factoid84

end DomainTheory.InformationSystems
