/-ai
The double fiber of an intersection is the intersection of the double fibers.

The two sides are definitionally equal.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

theorem fiber2_inter (S S' : Set (ℕ × (ℕ × α))) (i j : ℕ) :
    fiber2 (S ∩ S') i j = fiber2 S i j ∩ fiber2 S' i j := rfl

end Exercise718

end DomainTheory.NeighbourhoodSystems
