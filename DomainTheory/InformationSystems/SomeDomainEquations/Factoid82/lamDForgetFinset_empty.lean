/-ai
Forgetting the empty finite set of depth tokens yields the empty set of raw tokens.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


theorem lamDForgetFinset_empty : lamDForgetFinset A (∅ : Finset (LamDToken A)) = ∅ :=
  rfl

end InfoSys
end DomainTheory.InformationSystems
