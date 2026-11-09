module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.curryMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.element_toApproxMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.pairElements
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.uncurryMap
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.applyMap_toElement
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.curryMap_unique
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.elements_equiv_approxMaps
import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.uncurry_curryMap

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys
open ApproximableMap

theorem theorem_7_2 :
    (∀ {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β),
      (∀ f : ApproximableMap A B,
        element_toApproxMap A B (approxMap_toElement A B f) = f) ∧
      (∀ x : (functionSystem A B).Element,
        approxMap_toElement A B (element_toApproxMap A B x) = x)) ∧
    (∀ {β γ : Type*} [DecidableEq β] [DecidableEq γ] (B : InfoSys β) (C : InfoSys γ)
      (g : (functionSystem B C).Element) (y : B.Element),
      (applyMap (B := B) (C := C)).toElement
        (pairElements (functionSystem B C) B g y) =
        (element_toApproxMap B C g).toElement y) ∧
    (∀ {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
      (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)
      (h : ApproximableMap (productSystem A B) C)
      (k : ApproximableMap A (functionSystem B C)),
      uncurryMap A B C k = h → k = curryMap A B C h) ∧
    (∀ {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
      (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)
      (h : ApproximableMap (productSystem A B) C),
      uncurryMap A B C (curryMap A B C h) = h) :=
  ⟨@elements_equiv_approxMaps, @applyMap_toElement, @curryMap_unique, @uncurry_curryMap⟩

end DomainTheory.InformationSystems.InfoSys
