/-ai
The reindexing of a doubly indexed neighbourhood is the singly indexed set whose token at an index lies in the double fiber of the neighbourhood at the two components of the unpairing of that index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.EffectiveIso
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.mem_fiber2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.fiber2_reindexF

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

variable {V : NeighborhoodSystem α}

/-- The `D^∞`-set reindexing a `(D^∞)^∞`-neighbourhood `S`:
`fiber (reindexG S) k = fiber2 S (unpair k).1 (unpair k).2`. -/
def reindexG (S : Set (ℕ × (ℕ × α))) : Set (ℕ × α) :=
  {p | p.2 ∈ fiber2 S (Nat.unpair p.1).1 (Nat.unpair p.1).2}

end Exercise718

end DomainTheory.NeighbourhoodSystems
