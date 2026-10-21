/-ai
The value orUpTo n m N is the running bitwise disjunction, over set bits a strictly below N of n, of the shift of m by a places. The zero bound contributes 0. A successor bound disjoins the previous value with the shift of m by the current index when bitAt reports that the bit is set, and with 0 otherwise. This structural recursion is the reference specification of plusIdx.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.halfIter_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.bitAt
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic.notation16

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)

open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-- **Reference spec for `plusIdx`.** The running bitwise-OR of `m <<< a` over set bits `a < N` of
`n`, built by ordinary (non-primitive-recursive) structural recursion — used only to state and prove
correctness of the primitive-recursive `plusIdx` below. -/
def orUpTo (n m : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => myLor (orUpTo n m k) (selectFn (bitAt n k) (m <<< k) 0)

end DomainTheory.NeighbourhoodSystems.Exercise723
