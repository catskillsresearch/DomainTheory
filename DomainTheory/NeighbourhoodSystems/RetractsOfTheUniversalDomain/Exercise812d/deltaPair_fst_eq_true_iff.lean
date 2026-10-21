/-ai
The first component of deltaPair at depth i is true exactly when the base-four digit of k at place i is odd.

Unfold deltaPair and simplify.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718


































theorem deltaPair_fst_eq_true_iff (k i : ℕ) : (deltaPair k i).1 = true ↔ (k / 4 ^ i) % 2 = 1 := by
  unfold deltaPair; simp

end DomainTheory.NeighbourhoodSystems
