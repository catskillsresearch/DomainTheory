module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise823
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Pow
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Closing
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap







theorem isRetraction_cCombinator : IsRetraction cCombinator := by
  show (cInj.comp cProj).comp (cInj.comp cProj) = cInj.comp cProj
  rw [comp_assoc, ← comp_assoc cProj cInj cProj, cProj_comp_cInj, idMap_comp]

end DomainTheory.NeighbourhoodSystems
