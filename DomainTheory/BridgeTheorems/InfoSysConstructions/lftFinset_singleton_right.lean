module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
import all Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
import all Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem lftFinset_singleton_right (y : β) :
    lftFinset ({SumToken.right y} : Finset (SumToken α β)) = ∅ := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ ({SumToken.right y} : Finset _) := (mem_lftFinset).1 hx
    exact False.elim (nomatch Finset.mem_singleton.mp this)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

end InfoSysConstructions

end DomainTheory.BridgeTheorems
