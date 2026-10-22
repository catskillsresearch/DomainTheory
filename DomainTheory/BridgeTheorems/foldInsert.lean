module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.treeFold
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

def foldInsert (s : SumToken α (ProdToken (treeSystem A) (treeSystem A))) :
    Finset (TreeToken α) → Finset (TreeToken α) :=
  insert (treeFold A s)

end DomainTheory.BridgeTheorems
