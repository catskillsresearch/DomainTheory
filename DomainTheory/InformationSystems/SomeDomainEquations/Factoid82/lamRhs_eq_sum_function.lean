/-ai
The lambda right-hand side of an information system A equals the sum of A with the function space of the lambda system of A with itself.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


theorem lamRhs_eq_sum_function :
    lamRhs A = sumSystem A (functionSystem (lambdaSystem A) (lambdaSystem A)) :=
  rfl

end InfoSys
end DomainTheory.InformationSystems
