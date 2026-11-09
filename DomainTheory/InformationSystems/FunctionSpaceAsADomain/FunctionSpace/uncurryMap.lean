module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.applyMap
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product.pairMap

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

def uncurryMap (k : ApproximableMap A (functionSystem B C)) :
    ApproximableMap (productSystem A B) C :=
  comp (applyMap (B := B) (C := C))
    (pairMap (functionSystem B C) B (comp k (productSystem.fstMap A B)) (productSystem.sndMap A B))

end InfoSys

end DomainTheory.InformationSystems
