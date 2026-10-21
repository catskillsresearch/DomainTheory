/-ai
Atom insertion sends an atom token to insertion of its carrier, and sends the bottom token and every function token to the identity on finite sets of carriers.
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

def lamAtomInsert : RawLamToken α → Finset α → Finset α
  | .atom x => insert x
  | .bot | .funTok _ _ => id

end InfoSys

end DomainTheory.InformationSystems
