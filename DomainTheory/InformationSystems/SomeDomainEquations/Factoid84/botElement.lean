/-ai
The bottom element of the powerset system P is the entailment closure of the empty set of tokens.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.P

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid84

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

/-- Bottom element `⊥` of `|P|` (closure of `∅`). -/
def botElement : P.Element :=
  P.closure ∅ trivial

end Factoid84

end DomainTheory.InformationSystems
