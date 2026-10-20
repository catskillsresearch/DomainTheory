module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber_reindexG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Fmap_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Gmap_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

variable (P : ComputablePresentation V)

theorem fiber2_iterEnum_iter (m i j : ℕ) :
    fiber2 (iterEnum (iterPresentation P) m) i j
      = P.X (iterIdx P (iterIdx (iterPresentation P) m i) j) := by
  show fiber (fiber (iterEnum (iterPresentation P) m) i) j = _
  rw [fiber_iterEnum, iterPresentation_X, fiber_iterEnum]

end Exercise718

end DomainTheory.NeighbourhoodSystems
