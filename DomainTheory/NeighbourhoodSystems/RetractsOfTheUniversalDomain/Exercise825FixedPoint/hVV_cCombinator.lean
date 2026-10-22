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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825FixedPoint.fixedNbhd_cCombinator_isomorphic

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap


/-- **`fixedNbhd c × fixedNbhd c ≅ fixedNbhd c`**, transported from `Exercise825Pow.pow_prod_isomorphic`
along `fixedNbhd_cCombinator_isomorphic`. -/
theorem hVV_cCombinator :
    prod (fixedNbhd cCombinator) (fixedNbhd cCombinator) ≅ᴰ fixedNbhd cCombinator :=
  ((fixedNbhd_cCombinator_isomorphic.prod fixedNbhd_cCombinator_isomorphic).trans
    (pow_prod_isomorphic U)).trans fixedNbhd_cCombinator_isomorphic.symm

end DomainTheory.NeighbourhoodSystems
