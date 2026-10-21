/-ai
The flat BOOL information system is the information system produced by Factoid 2.5 from BOOL satisfaction, taking the bottom token as the distinguished token, using that every point satisfies the bottom token and that every token is satisfied by some point.
ai-/

module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSat
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSat_bot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSat_sing

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

/-- **Factoid 7.5.** Flat BOOL information system. -/
def boolSystem : InfoSys BoolToken :=
  Factoid25.ofSatisfaction boolSat .bot boolSat_bot boolSat_sing

end InfoSys

end DomainTheory.InformationSystems
