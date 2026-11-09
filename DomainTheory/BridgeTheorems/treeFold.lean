module

public import DomainTheory.InformationSystems.SomeDomainEquations.treeSystem

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.InfoSys
open treeSystem

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

def treeFold :
    SumToken α (ProdToken (treeSystem A) (treeSystem A)) → TreeToken α
  | .bot => .bot
  | .left x => .atom x
  | .right p =>
      if p.val.2 = treeBot then .pairL p.val.1 else .pairR p.val.2

end DomainTheory.BridgeTheorems
