module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.example_8_1
public import DomainTheory.InformationSystems.SomeDomainEquations.treeSystem

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys
open treeSystem

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

def unfoldInsert (t : TreeToken α) :
    Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A))) →
      Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A))) :=
  insert (treeUnfold A t)

end DomainTheory.BridgeTheorems
