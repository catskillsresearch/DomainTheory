/-ai
If one doubly indexed set is contained in another, then every double fiber of the first is contained in the corresponding double fiber of the second.

A token of the double fiber lies in the first set, hence in the second.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

theorem fiber2_mono {S S' : Set (ℕ × (ℕ × α))} (h : S ⊆ S') (i j : ℕ) :
    fiber2 S i j ⊆ fiber2 S' i j := fun _ ha => h ha

end Exercise718

end DomainTheory.NeighbourhoodSystems
