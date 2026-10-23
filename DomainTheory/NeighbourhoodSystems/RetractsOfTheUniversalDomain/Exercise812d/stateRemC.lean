module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise718
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812d.other_2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_2

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

def stateRemC (t : ℕ) : ℕ := t.unpair.1

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace stateRemC

open NeighborhoodSystem Domain.Recursive ApproximableMap Exercise718

@[simp] theorem packStateC (a b : ℕ) : stateRemC (_root_.DomainTheory.NeighbourhoodSystems.packStateC a b) = a := by
  unfold stateRemC _root_.DomainTheory.NeighbourhoodSystems.packStateC; simp only [unpair_pair_fst]

end stateRemC
end DomainTheory.NeighbourhoodSystems
