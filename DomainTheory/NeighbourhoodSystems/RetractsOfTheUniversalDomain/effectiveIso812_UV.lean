module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Vunion
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.effectiveIso812d
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18
public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.Nat.Bitwise
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem Exercise718

noncomputable def effectiveIso812_UV : EffectiveIso UComputablePresentation VComputablePresentation :=
  effectiveIso812d UComputablePresentation VComputablePresentation U_isComputableDiff
    V.isComputableDiff splitX812e isComputableSplit.«812e» splitX812f isComputableSplit.«812f»
    U.isPositive U.diffClosed U.noMinimal hxSplit812e V.isPositive V.diffClosed V.noMinimal
    hySplit812f U_master_nonempty V.master_nonempty U_isComputableUnion V.isComputableUnion UX_zero
    VX_zero

end DomainTheory.NeighbourhoodSystems
