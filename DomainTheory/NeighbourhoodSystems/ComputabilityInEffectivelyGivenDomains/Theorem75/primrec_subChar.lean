/-ai
If both inclusion characteristics are primitive recursive, then the function sending a paired code to the step-function inclusion characteristic of its two components is primitive recursive.

That characteristic is the fold of the primitive-recursive inclusion step, with the left projection as parameter, the constant 1 as the start, and the right projection as the list code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.subChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.primrec_subStp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

theorem primrec_subChar (incl0 incl1 : ℕ → ℕ) (hincl0p : Nat.Primrec incl0)
    (hincl1p : Nat.Primrec incl1) :
    Nat.Primrec (fun t => subChar P₁ incl0 incl1 t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_subStp P₁ incl0 incl1 hincl0p hincl1p) Nat.Primrec.left
    (Nat.Primrec.const 1) Nat.Primrec.right).of_eq (fun _ => rfl)

end DomainTheory.NeighbourhoodSystems
