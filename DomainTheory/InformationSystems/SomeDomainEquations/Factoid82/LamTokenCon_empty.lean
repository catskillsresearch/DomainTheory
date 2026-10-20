module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamCon_empty
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamForgetFinset_empty

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)

















theorem LamTokenCon_empty : LamTokenCon A (∅ : Finset (LamToken A)) := by
  simpa [LamTokenCon, lamForgetFinset_empty] using LamCon_empty A

end InfoSys
end DomainTheory.InformationSystems
