module
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.pairElements
import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.productSystem_more

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem pairElements_unpair (z : (productSystem A B).Element) :
    pairElements A B ((productSystem.fstMap A B).toElement z) ((productSystem.sndMap A B).toElement z) = z :=
  productSystem.element_eq_of_fst_snd A B _ z (fstMap_pairElements A B _ _) (sndMap_pairElements A B _ _)

end InfoSysConstructions

end DomainTheory.BridgeTheorems
