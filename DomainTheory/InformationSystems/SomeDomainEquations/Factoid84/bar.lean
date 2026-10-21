/-ai
Scott's bar notation sends a natural number n to the singleton finite set whose only token is n.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35

@[expose] public section

namespace DomainTheory.InformationSystems

namespace Factoid84

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

/-- Scott’s shorthand `\bar n = {n}` as a finite set of tokens. -/
def bar (n : ℕ) : Finset ℕ := {n}

end Factoid84

end DomainTheory.InformationSystems
