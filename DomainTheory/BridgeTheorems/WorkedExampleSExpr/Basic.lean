module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.sexAtom
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.sexRhsSemanticIso
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.sexDomainEquationIso

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.InfoSys.ApproximableMap
open Order

noncomputable abbrev sexNeighborhoodIso :
    SexSys.Element ≃o (InfoSysToNeighborhood.toNeighborhoodSystem SexSys).Element :=
  InfoSysToNeighborhood.domainOrderIso SexSys

noncomputable abbrev sexIdealIso :
    SexSys.Element ≃o Ideal (InfoSysToIdealCompletion.FiniteElement SexSys) :=
  InfoSysToIdealCompletion.domainOrderIso SexSys

noncomputable abbrev sexNeighborhoodIdealIso :=
  neighborhood_ideal_iso SexSys

noncomputable abbrev sexIdScottContinuous : ScottContinuous SexSys SexSys :=
  (approximableMap_scottContinuous_equiv SexSys SexSys) (idMap SexSys)
end DomainTheory.BridgeTheorems
