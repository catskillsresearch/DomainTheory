/-ai
The intersection of two enumerated infinite-iterate neighbourhoods equals a third exactly when the fiber neighbourhoods agree at every coordinate below the sum of the three codes.

Applying the fiber operation to the equality gives one direction. Conversely the two sides have the same fibers: below the bound by the hypothesis, and beyond it because each fiber index is the master index, so both sides equal the master neighbourhood.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.ScottPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₀_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashProj₁_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.smashPaired_rel
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osum_master
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.osumPresentation_X
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.fiber_iterEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterIdx_ge

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

open Exercise510

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

variable {P}

/-- **Relation (i) reduces to a bounded coordinate check.** `iterEnum n ∩ iterEnum m = iterEnum k`
iff fiber-wise equality holds for all `j` below `n+m+k` (beyond which every fiber is `Δ`). -/
theorem iterEnum_inter_eq_iff {n m k : ℕ} :
    iterEnum P n ∩ iterEnum P m = iterEnum P k ↔
      ∀ j, j < n + m + k →
        P.X (iterIdx P n j) ∩ P.X (iterIdx P m j) = P.X (iterIdx P k j) := by
  constructor
  · intro h j _
    have := congrArg (fun W => fiber W j) h
    simpa only [fiber_inter, fiber_iterEnum] using this
  · intro h
    apply eq_of_fiber_eq
    intro j
    rw [fiber_inter, fiber_iterEnum, fiber_iterEnum, fiber_iterEnum]
    by_cases hj : j < n + m + k
    · exact h j hj
    · rw [iterIdx_ge (show n ≤ j by omega), iterIdx_ge (show m ≤ j by omega),
        iterIdx_ge (show k ≤ j by omega), P.masterIdx_spec, Set.inter_self]

end Iterate

end DomainTheory.NeighbourhoodSystems
