module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.compOp

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys
open ApproximableMap

theorem theorem_76 :
    ∀ {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
      (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)
      (g : ApproximableMap B C) (f : ApproximableMap A B),
      (compOp A B C).toElement
        (pairElements (functionSystem B C) (functionSystem A B)
          (approxMap_toElement B C g) (approxMap_toElement A B f)) =
        approxMap_toElement A C (comp g f) :=
  @compOp.toElement

end DomainTheory.InformationSystems.InfoSys
