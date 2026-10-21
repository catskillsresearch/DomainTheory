/-ai
If the domain inclusion characteristic is primitive recursive, then the function sending a paired code to the conditional output-intersection index of its two components is primitive recursive.

That index is the fold of the primitive-recursive step, with the right projection as parameter, the master index as the constant start, and the left projection as the list code, and the fold agrees with the paired index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interYsIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.primrec_interYsStp

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

theorem primrec_interYsIdx (incl0 : ℕ → ℕ) (hincl0p : Nat.Primrec incl0) :
    Nat.Primrec (fun t => interYsIdx P₁ incl0 t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_interYsStp P₁ incl0 hincl0p) Nat.Primrec.right
    (Nat.Primrec.const P₁.masterIdx) Nat.Primrec.left).of_eq (fun _ => rfl)

end DomainTheory.NeighbourhoodSystems
