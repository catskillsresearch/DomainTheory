module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.BridgeTheorems.unfoldInsert
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

def unfoldFinset (u : Finset (TreeToken α)) :
    Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A))) :=
  Multiset.foldr (unfoldInsert A) ∅ u.1

end DomainTheory.BridgeTheorems
