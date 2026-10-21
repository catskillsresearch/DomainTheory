/-ai
The double fiber of the reindexing of a singly indexed neighbourhood, at i and j, is the fiber of that neighbourhood at the pairing of i and j.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.reindexF

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

@[simp] theorem fiber2_reindexF (W : Set (ℕ × α)) (i j : ℕ) :
    fiber2 (reindexF W) i j = fiber W (Nat.pair i j) := rfl

end Exercise718

end DomainTheory.NeighbourhoodSystems
