module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.approxMap_toElement

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

open ApproximableMap

theorem mem_approxMap_toElement (f : ApproximableMap A B) {p : FunToken A B} :
    p ∈ (approxMap_toElement A B f).carrier ↔ f.rel p.val.1 p.val.2 :=
  Iff.rfl

end InfoSys
end DomainTheory.InformationSystems
