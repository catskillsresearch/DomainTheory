module
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.pairElements
public import DomainTheory.InformationSystems.InformationSystems.InfoSys.Basic
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

theorem pairElements_mono {x₁ x₂ : A.Element} {y₁ y₂ : B.Element}
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    pairElements A B x₁ y₁ ≤ pairElements A B x₂ y₂ := by
  intro p hp
  exact ⟨fun hbot => hx (hp.1 hbot), fun hbot => hy (hp.2 hbot)⟩

end InfoSysConstructions

end DomainTheory.BridgeTheorems
