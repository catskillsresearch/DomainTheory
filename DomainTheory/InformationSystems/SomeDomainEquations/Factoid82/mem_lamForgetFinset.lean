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

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)












theorem mem_lamForgetFinset {u : Finset (LamToken A)} {t : RawLamToken α} :
    t ∈ lamForgetFinset A u ↔ ∃ p ∈ u, p.val = t := by
  simpa [lamForgetFinset] using mem_foldr_lamForget A u.1 t

end InfoSys
end DomainTheory.InformationSystems
