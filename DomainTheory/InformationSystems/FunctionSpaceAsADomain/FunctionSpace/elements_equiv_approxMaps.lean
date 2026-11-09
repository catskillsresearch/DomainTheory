module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.element_toApproxMap
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.approxMap_toElement_element_toApproxMap

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem elements_equiv_approxMaps {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    (∀ f : ApproximableMap A B,
      element_toApproxMap A B (approxMap_toElement A B f) = f) ∧
    (∀ x : (functionSystem A B).Element,
      approxMap_toElement A B (element_toApproxMap A B x) = x) :=
  ⟨element_toApproxMap.approxMap_toElement A B,
    approxMap_toElement_element_toApproxMap A B⟩

end InfoSys
end DomainTheory.InformationSystems
