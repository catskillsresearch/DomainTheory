/-ai
The map unfoldInsert, at a tree token, inserts the tree unfold of that token into a finite set of sum tokens.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

def unfoldInsert (t : TreeToken α) :
    Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A))) →
      Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A))) :=
  insert (treeUnfold A t)

end DomainTheory.BridgeTheorems
