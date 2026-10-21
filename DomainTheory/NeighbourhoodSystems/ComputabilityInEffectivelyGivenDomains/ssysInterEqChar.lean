/-ai
The intersection-equality characteristic of a packed triple of indices is the intersection-equality characteristic, at fuel the sum of the three stored depths plus three, of the intersection code of the canonical codes of the first two indices against the canonical code of the third. The triple is packed as the pairing of the first index with the pairing of the second and the third.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysCanonicalCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

/-- **Exercise 7.22k.** `{0,1}` decider for Definition 7.1 relation (i) on `SsysX` indices,
`Nat.pair`-coded as `pair n (pair m k)`. -/
def ssysInterEqChar (t : ℕ) : ℕ :=
  let n := t.unpair.1
  let m := t.unpair.2.unpair.1
  let k := t.unpair.2.unpair.2
  Domain.Recursive.interEqChar (n.unpair.2 + m.unpair.2 + k.unpair.2 + 3)
    (Domain.Recursive.capCode (ssysCanonicalCode n) (ssysCanonicalCode m)) (ssysCanonicalCode k)

end Exercise722

end DomainTheory.NeighbourhoodSystems
