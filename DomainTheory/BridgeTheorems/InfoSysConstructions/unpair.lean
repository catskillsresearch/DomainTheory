module
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.productSystem
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.toElement
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.proposition_6_4

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

def unpair (z : (productSystem A B).Element) : A.Element × B.Element :=
  ((productSystem.fstMap A B).toElement z, (productSystem.sndMap A B).toElement z)

end InfoSysConstructions

end DomainTheory.BridgeTheorems
