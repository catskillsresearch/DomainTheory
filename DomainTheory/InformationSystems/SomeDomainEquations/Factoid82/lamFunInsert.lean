module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

def lamFunInsert :
    RawLamToken α → Finset (List (RawLamToken α) × List (RawLamToken α)) →
      Finset (List (RawLamToken α) × List (RawLamToken α))
  | .funTok u v => insert (u, v)
  | .bot | .atom _ => id

end InfoSys

end DomainTheory.InformationSystems
