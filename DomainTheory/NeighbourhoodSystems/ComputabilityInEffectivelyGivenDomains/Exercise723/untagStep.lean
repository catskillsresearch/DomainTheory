/-ai
The untagging transition leaves its state unchanged once the done flag is set, and otherwise peels one layer of the numeral decoding. If the first component of that decoding is zero, it pairs the second component with the flag one, the reversed accumulator, and that second component. Otherwise it pairs the second component with the flag zero, the successor of the pairing of the predecessor of the first component with the reversed accumulator, and the carried value.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.halfIter_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.mem_elemSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.unnum1
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.unnum2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic.notation16

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)

open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-- The state-transition step: no-op once `done`; otherwise peel one `unnum` layer. -/
def untagStep (w : ℕ) : ℕ :=
  selectFn w.unpair.2.unpair.1 w
    (selectFn (isZero (unnum1 w.unpair.1))
      (Nat.pair (unnum2 w.unpair.1)
        (Nat.pair 1 (Nat.pair w.unpair.2.unpair.2.unpair.1 (unnum2 w.unpair.1))))
      (Nat.pair (unnum2 w.unpair.1)
        (Nat.pair 0
          (Nat.pair (Nat.pair (unnum1 w.unpair.1 - 1) w.unpair.2.unpair.2.unpair.1 + 1)
            w.unpair.2.unpair.2.unpair.2))))

end DomainTheory.NeighbourhoodSystems.Exercise723
