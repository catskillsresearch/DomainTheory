/-ai
The finite set associated with a list is empty when the list is empty, and otherwise inserts the head into the finite set of the tail.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

def listToFinset {β : Type*} [DecidableEq β] : List β → Finset β
  | [] => ∅
  | x :: xs => insert x (listToFinset xs)

end InfoSys

end DomainTheory.InformationSystems
