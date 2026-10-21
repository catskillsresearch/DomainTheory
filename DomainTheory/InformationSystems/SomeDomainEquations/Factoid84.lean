/-ai
The identity map of the powerset system P fails Scott's rogue condition.

The numbered name theorem_84 is that statement.
ai-/
module

public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.not_RogueApprox_idMap

@[expose] public section

namespace DomainTheory.InformationSystems.Factoid84

set_option linter.unusedVariables false

theorem theorem_84 : Not
  (DomainTheory.InformationSystems.Factoid84.RogueApprox
    (@DomainTheory.InformationSystems.InfoSys.idMap Nat instDecidableEqNat DomainTheory.InformationSystems.Factoid84.P)) :=
  DomainTheory.InformationSystems.Factoid84.not_RogueApprox_idMap

end DomainTheory.InformationSystems.Factoid84
