module
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.productSystem
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.toElement

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
