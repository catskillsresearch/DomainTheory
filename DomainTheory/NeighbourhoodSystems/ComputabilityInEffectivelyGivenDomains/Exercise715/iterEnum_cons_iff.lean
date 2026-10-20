/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterInter
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterInter_idx_lt
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterInter_idx_ge

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

/-- **Relation (ii) reduces to a bounded coordinate check.** `iterEnum n ∩ iterEnum m` is consistent
iff every coordinate `j < n+m` is consistent in `V`. The witness is `iterInter n m`. -/
theorem iterEnum_cons_iff {n m : ℕ} :
    (∃ k, iterEnum P k ⊆ iterEnum P n ∩ iterEnum P m) ↔
      ∀ j, j < n + m → ∃ i, P.X i ⊆ P.X (iterIdx P n j) ∩ P.X (iterIdx P m j) := by
  constructor
  · rintro ⟨k, hk⟩ j _
    refine ⟨iterIdx P k j, ?_⟩
    have := fiber_mono hk j
    rwa [fiber_inter, fiber_iterEnum, fiber_iterEnum, fiber_iterEnum] at this
  · intro h
    refine ⟨iterInter P n m, ?_⟩
    apply subset_of_fiber_subset
    intro j
    rw [fiber_inter, fiber_iterEnum, fiber_iterEnum, fiber_iterEnum]
    by_cases hj : j < n + m
    · rw [iterInter_idx_lt hj]
      obtain ⟨i, hi⟩ := h j hj
      rw [P.inter_spec ⟨i, hi⟩]
    · rw [iterInter_idx_ge (by omega), iterIdx_ge (show n ≤ j by omega),
        iterIdx_ge (show m ≤ j by omega), P.masterIdx_spec, Set.inter_self]

end Iterate

end DomainTheory.NeighbourhoodSystems
