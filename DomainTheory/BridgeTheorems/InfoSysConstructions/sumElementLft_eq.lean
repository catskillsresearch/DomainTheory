module
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64.sumElementLft
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


theorem sumElementLft_eq {z : (sumSystem A B).Element} {x0 x1 : α}
    (hx0 : SumToken.left x0 ∈ z.carrier) (hx1 : SumToken.left x1 ∈ z.carrier) :
    sumElementLft A B z x0 hx0 = sumElementLft A B z x1 hx1 := by
  refine le_antisymm ?_ ?_ <;> intro a ha <;> exact ha

end InfoSysConstructions
end DomainTheory.BridgeTheorems
