module
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.pairElements
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.productSystem_more
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.toElement
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.theorem_7_2
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.proposition_6_4

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem pairElements_unpair (z : (productSystem A B).Element) :
    pairElements A B ((productSystem.fstMap A B).toElement z) ((productSystem.sndMap A B).toElement z) = z :=
  productSystem.element_eq_of_fst_snd A B _ z (fstMap_pairElements A B _ _) (sndMap_pairElements A B _ _)

end InfoSysConstructions

end DomainTheory.BridgeTheorems
