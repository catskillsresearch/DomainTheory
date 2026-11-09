module

public import DomainTheory.BridgeTheorems.treeFold

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.InfoSys
open treeSystem

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

def foldInsert (s : SumToken α (ProdToken (treeSystem A) (treeSystem A))) :
    Finset (TreeToken α) → Finset (TreeToken α) :=
  insert (treeFold A s)

end DomainTheory.BridgeTheorems
