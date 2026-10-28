
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

def FixChain (w : Finset (FunToken A A)) : Nat → Finset α → Prop
  | 0, v => v = ∅
  | n + 1, v =>
      ∃ u : Finset α, FixChain w n u ∧
        ∃ (hu : u ∈ A.Con) (hv : v ∈ A.Con),
          FunEnt A A w (mkFunToken A A u v hu hv)

end InfoSys

end DomainTheory.InformationSystems
