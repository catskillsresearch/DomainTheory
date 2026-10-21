/-ai
The value halfIter n k is the k-fold iteration of integer division by 2, applied to n. It is the primitive-recursive core of the binary digit test.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.Fun_mono
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.num_succ_left_gt
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_injective

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)

open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-- Iterated halving `(·/2)^[k] n`, the primitive-recursive core of `Nat.testBit`. -/
def halfIter (n k : ℕ) : ℕ := (fun x : ℕ => x / 2)^[k] n

end DomainTheory.NeighbourhoodSystems.Exercise723
