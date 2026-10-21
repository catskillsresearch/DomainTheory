/-ai
Function insertion sends a function token to insertion of its input-output pair, and sends the bottom token and every atom token to the identity on finite sets of such pairs.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

def lamFunInsert :
    RawLamToken α → Finset (List (RawLamToken α) × List (RawLamToken α)) →
      Finset (List (RawLamToken α) × List (RawLamToken α))
  | .funTok u v => insert (u, v)
  | .bot | .atom _ => id

end InfoSys

end DomainTheory.InformationSystems
