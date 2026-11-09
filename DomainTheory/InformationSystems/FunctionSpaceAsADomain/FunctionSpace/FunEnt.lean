module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.FunCon

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

def FunEnt (w : Finset (FunToken A B)) (p : FunToken A B) : Prop :=
  FunCon A B w ∧
    ∃ s ⊆ w, (∀ q ∈ s, A.EntSet p.val.1 q.val.1) ∧
      B.EntSet (funOutputUnion A B s) p.val.2

end InfoSys

end DomainTheory.InformationSystems
