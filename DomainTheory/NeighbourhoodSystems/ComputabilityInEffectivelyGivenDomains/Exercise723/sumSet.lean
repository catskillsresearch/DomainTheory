/-ai
Scott's sum of two sets of natural numbers is their Minkowski sum. A natural number lies in the sum when it is the ordinary sum of a member of the first set and a member of the second.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.halfIter_zero

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive

open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)

open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)

/-- Scott's `x + y = {n+m ∣ n ∈ x, m ∈ y}` (Minkowski sum) for `x, y ⊆ ℕ`. -/
def sumSet (X Y : Set ℕ) : Set ℕ := {k | ∃ a ∈ X, ∃ b ∈ Y, a + b = k}

end DomainTheory.NeighbourhoodSystems.Exercise723
