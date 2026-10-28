module
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition53.Le
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable.ext
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

instance instPartialOrderApproximableMap : PartialOrder (ApproximableMap A B) where
  le := @Le _ _ _ _ A B
  le_refl _ _ _ h := h
  le_trans _ _ _ hfg hgh _ _ hf := hgh (hfg hf)
  le_antisymm _ _ hfg hgf := ApproximableMap.ext fun _ _ => ⟨fun h => hfg h, fun h => hgf h⟩

end InfoSysConstructions

end DomainTheory.BridgeTheorems
