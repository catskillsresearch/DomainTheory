module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_8
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace deltaPair

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718


theorem fst_eq_true_iff (k i : ℕ) : (deltaPair k i).1 = true ↔ (k / 4 ^ i) % 2 = 1 := by
  unfold deltaPair; simp

end deltaPair
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace deltaPair

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718


theorem snd_eq_true_iff (k i : ℕ) : (deltaPair k i).2 = true ↔ (k / 4 ^ i / 2) % 2 = 1 := by
  unfold deltaPair; simp

end deltaPair
end DomainTheory.NeighbourhoodSystems
