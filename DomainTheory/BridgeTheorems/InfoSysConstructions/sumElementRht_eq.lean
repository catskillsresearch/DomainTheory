module
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.sumElementRht
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64
public import DomainTheory.BridgeTheorems.InfoSysConstructions.Basic

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem sumElementRht_eq {z : (sumSystem A B).Element} {y0 y1 : β}
    (hy0 : SumToken.right y0 ∈ z.carrier) (hy1 : SumToken.right y1 ∈ z.carrier) :
    sumElementRht A B z y0 hy0 = sumElementRht A B z y1 hy1 := by
  refine le_antisymm ?_ ?_ <;> intro b hb <;> exact hb

end InfoSysConstructions
end DomainTheory.BridgeTheorems
