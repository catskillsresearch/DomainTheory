/-ai
If a function on codes is primitive recursive, then so is the function sending a code to the fiber index of its value at the code's first component.

Primitive-recursive list lookup, applied to that function, the first component, and the constant master index, simplifies to this fiber index.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.fiber_iterEnum

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

/-- Primitive recursivity of `fun w ↦ iterIdx (codeProj w) (w.unpair.1)` for a primrec `codeProj`. -/
theorem primrec_iterIdx_proj {codeProj : ℕ → ℕ} (hc : Nat.Primrec codeProj) :
    Nat.Primrec (fun w => iterIdx P (codeProj w) w.unpair.1) := by
  refine (primrec_nthCode.comp (hc.pair (Nat.Primrec.left.pair
    (Nat.Primrec.const P.masterIdx)))).of_eq (fun w => ?_)
  simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]

end Iterate

end DomainTheory.NeighbourhoodSystems
