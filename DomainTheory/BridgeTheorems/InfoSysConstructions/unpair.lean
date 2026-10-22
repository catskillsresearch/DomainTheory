/-ai
Unpairing splits an element of a product of information systems into the pair of its images under the first and second projections.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

/-- Split a product-domain element into its two projections. -/
def unpair (z : (productSystem A B).Element) : A.Element × B.Element :=
  ((fstMap A B).toElement z, (sndMap A B).toElement z)

end InfoSysConstructions

end DomainTheory.BridgeTheorems
