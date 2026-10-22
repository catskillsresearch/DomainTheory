module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.NeighborhoodSystemu2eIsEffectivelyGivenu2etoS
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

/-- The `(D^∞)^∞`-set reindexing a `D^∞`-neighbourhood `W`: `fiber2 (reindexF W) i j = fiber W (pair i j)`. -/
def reindexF (W : Set (ℕ × α)) : Set (ℕ × (ℕ × α)) :=
  {p | p.2.2 ∈ fiber W (Nat.pair p.1 p.2.1)}

end Exercise718

end DomainTheory.NeighbourhoodSystems
