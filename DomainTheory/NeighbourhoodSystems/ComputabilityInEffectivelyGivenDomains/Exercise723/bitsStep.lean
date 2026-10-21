/-ai
The step bitsStep advances the packed state (n, N, acc) of the bitsCode iteration. It leaves n unchanged, replaces N by N + 1, and replaces the accumulator by the cons of N onto acc when the N-th bit of n is set, and by acc otherwise. The cons is coded by pairing N with acc and adding one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.halfIter_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.bitAt
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_elemSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic.notation16

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)

open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-- The primitive-recursive step function for `bitsCode`'s iteration: `(n, N, acc) ↦
(n, N+1, if n.testBit N then pair N acc + 1 else acc)`. -/
def bitsStep (s : ℕ) : ℕ :=
  Nat.pair s.unpair.1
    (Nat.pair (s.unpair.2.unpair.1 + 1)
      (selectFn (bitAt s.unpair.1 s.unpair.2.unpair.1)
        (Nat.pair s.unpair.2.unpair.1 s.unpair.2.unpair.2 + 1) s.unpair.2.unpair.2))

end DomainTheory.NeighbourhoodSystems.Exercise723
