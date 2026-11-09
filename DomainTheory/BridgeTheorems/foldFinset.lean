module

public import DomainTheory.BridgeTheorems.SexDomainEquationInst15

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.InfoSys
open treeSystem

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

def foldFinset (Y : Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A)))) :
    Finset (TreeToken α) :=
  Multiset.foldr (foldInsert A) ∅ Y.1

end DomainTheory.BridgeTheorems
