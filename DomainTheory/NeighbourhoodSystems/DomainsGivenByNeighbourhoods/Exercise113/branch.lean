module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.prefixSeq_length
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.branchSeq
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise113.branchSeq_mono

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise113

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ExampleB

/-- **The limit/total element of an infinite path** `p`: the ascending union `⋃ₙ (p ↾ n)⊥`
(Theorem 1.11(ii)). These are the "limit nodes all along the top" of Scott's picture. -/
def branch (p : ℕ → Bool) : B.Element := B.iUnion (branchSeq p) (branchSeq_mono p)

end DomainTheory.NeighbourhoodSystems.Exercise113
