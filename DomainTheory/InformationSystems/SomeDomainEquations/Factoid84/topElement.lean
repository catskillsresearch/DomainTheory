/-ai
The top element of the powerset system P is the top element obtained from the fact that every finite set of tokens of P is consistent. Its carrier contains every token.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.P
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.P_AllConsistent

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid84

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

/-- Top element `⊤` of `|P|` (all tokens). -/
def topElement : P.Element :=
  P.topElement P_AllConsistent

end Factoid84

end DomainTheory.InformationSystems
