module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.Basic

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open treeSystem
open DomainTheory.InformationSystems.InfoSys.ApproximableMap
open Order

theorem sexRhs_eq_sum_product :
    SexRhs = sumSystem lowerBoundSystem (productSystem SexSys SexSys) :=
  treeRhs.eq_sum_product lowerBoundSystem

end DomainTheory.BridgeTheorems
