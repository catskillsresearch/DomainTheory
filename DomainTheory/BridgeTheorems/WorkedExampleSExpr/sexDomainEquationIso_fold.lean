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

theorem sexDomainEquationIso_fold (y : SexRhs.Element) :
    (sexDomainEquationIso.symm y).carrier =
      treeUnfold lowerBoundSystem ⁻¹' y.carrier :=
  rfl

end DomainTheory.BridgeTheorems
