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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.fiber_iterEnum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.interG
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.iterInter

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

theorem iterInter_idx_lt {n m j : ℕ} (hj : j < n + m) :
    iterIdx P (iterInter P n m) j = P.inter (iterIdx P n j) (iterIdx P m j) := by
  show nthCode (iterInter P n m) j P.masterIdx = _
  rw [iterInter, tabCode_nth_lt hj]
  unfold interG
  simp only [unpair_pair_fst, unpair_pair_snd]

end Iterate

end DomainTheory.NeighbourhoodSystems
