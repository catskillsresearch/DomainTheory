/-ai
The second component of deltaPair at depth i is true exactly when the next bit of the base-four digit of k at place i is set.

Unfold deltaPair and simplify.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.Basic

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.mem_ne_empty
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718


































theorem deltaPair_snd_eq_true_iff (k i : ℕ) : (deltaPair k i).2 = true ↔ (k / 4 ^ i / 2) % 2 = 1 := by
  unfold deltaPair; simp

end DomainTheory.NeighbourhoodSystems
