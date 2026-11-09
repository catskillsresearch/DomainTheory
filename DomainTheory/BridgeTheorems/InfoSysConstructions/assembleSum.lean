module
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.inrMap
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum.inlMap
public import Mathlib.Order.TypeTags

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

def assembleSum : WithBot (A.Element ⊕ B.Element) → (sumSystem A B).Element
  | ⊥ => (sumSystem A B).botElement
  | some (.inl x) => (inlMap A B).toElement x
  | some (.inr y) => (inrMap A B).toElement y

end InfoSysConstructions

end DomainTheory.BridgeTheorems
