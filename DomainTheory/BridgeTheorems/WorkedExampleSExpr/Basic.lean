module

public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.sexAtom
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.sexRhsSemanticIso
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.sexDomainEquationIso

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems.InfoSys
open Order

noncomputable abbrev sexNeighborhoodIso :
    SexSys.Element ≃o (InfoSysToNeighborhood.toNeighborhoodSystem SexSys).Element :=
  InfoSysToNeighborhood.domainOrderIso SexSys

noncomputable abbrev sexIdealIso :
    SexSys.Element ≃o Ideal (InfoSysToIdealCompletion.FiniteElement SexSys) :=
  InfoSysToIdealCompletion.domainOrderIso SexSys

noncomputable abbrev sexNeighborhoodIdealIso :=
  neighborhood_ideal_iso SexSys

/-- SExpr landing: 1982 ≃o 1980. -/
noncomputable abbrev sex_bridge_1982_1980 := sexNeighborhoodIso

/-- SExpr landing: 1982 ≃o 1972 algebraic carrier. -/
noncomputable abbrev sex_bridge_1982_1972 := sexIdealIso

noncomputable abbrev sexIdScottContinuous : ScottContinuous SexSys SexSys :=
  (approximableMap_scottContinuous_equiv SexSys SexSys) (idMap SexSys)
end DomainTheory.BridgeTheorems
