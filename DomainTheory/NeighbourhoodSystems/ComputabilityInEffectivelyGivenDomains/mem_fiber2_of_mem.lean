module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

/-- `V.mem (fiber2 S i j)` for every `(D^∞)^∞`-neighbourhood `S`. -/
theorem mem_fiber2_of_mem {S : Set (ℕ × (ℕ × α))} (hS : (iterSys (iterSys V)).mem S) (i j : ℕ) :
    V.mem (fiber2 S i j) := (hS.1 i).1 j

end Exercise718

end DomainTheory.NeighbourhoodSystems
