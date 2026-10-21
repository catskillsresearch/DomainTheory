/-ai
The equality bit of a packed equality bit, consistency bit, and intersection index is the equality bit.

Unfolding the equality bit and the packing, the first pairing projection returns that component.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.packT
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.eqB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

@[simp] theorem eqB_packT (e c ii : ℕ) : eqB (packT e c ii) = e := by
  simp only [eqB, packT, unpair_pair_fst]

end Proposition77

end DomainTheory.NeighbourhoodSystems
