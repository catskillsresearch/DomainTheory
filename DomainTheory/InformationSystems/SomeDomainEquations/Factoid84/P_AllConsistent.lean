/-ai
Every finite set of tokens of the powerset information system P is consistent.

Consistency on P is the universally true predicate, so the claim holds outright.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.P

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid84

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

theorem P_AllConsistent : P.AllConsistent := fun _ => trivial

end Factoid84

end DomainTheory.InformationSystems
