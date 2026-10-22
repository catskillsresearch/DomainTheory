module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

theorem inter_diff_self_eq_empty {γ : Type*} (P Q : Set γ) : (P ∩ Q) ∩ (P \ Q) = ∅ := by
  ext x; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]; tauto

end DomainTheory.NeighbourhoodSystems
