/-ai
The flat map sends the finite element of 1 to the top element of the powerset system P.

The token 1 belongs to that finite element, and the flat map sends every element containing 1 to the top element.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.mem_barElement
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap_toElement_of_mem_one

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

theorem flatMap_rogue : RogueApprox flatMap :=
  flatMap_toElement_of_mem_one ((mem_barElement 1 1).2 (Or.inr rfl))

end Factoid84

end DomainTheory.InformationSystems
