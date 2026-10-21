/-ai
The fold of a finite set of right-hand-side tokens is the finite set of tree tokens obtained by inserting, through a choice-free fold, the tree fold of each token into the empty set.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.foldInsert
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Choice-free image of an RHS finset under `treeFold`. -/
def foldFinset (Y : Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A)))) :
    Finset (TreeToken α) :=
  Multiset.foldr (foldInsert A) ∅ Y.1

end DomainTheory.BridgeTheorems
