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

theorem sexDomainEquationIso_unfold (x : SexSys.Element) :
    (sexDomainEquationIso x).carrier =
      treeUnfold lowerBoundSystem '' x.carrier :=
  rfl

end DomainTheory.BridgeTheorems
