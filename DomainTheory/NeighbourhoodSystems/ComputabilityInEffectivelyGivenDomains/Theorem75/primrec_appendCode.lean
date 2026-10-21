/-ai
The function sending a paired code to the append code of its two components is primitive recursive.

The append step is primitive recursive as addition of a pairing of the left projection with the left of the right projection and the constant 1. The append code is the fold of that step from the constant 0, and the fold agrees with the paired append code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.appendStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.appendCode

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

theorem primrec_appendCode : Nat.Primrec (fun t => appendCode t.unpair.1 t.unpair.2) := by
  have hstp : Nat.Primrec appendStp :=
    (primrec_add₂ (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right))
      (Nat.Primrec.const 1)).of_eq (fun w => rfl)
  exact (primrec_foldCode hstp (Nat.Primrec.const 0) Nat.Primrec.left Nat.Primrec.right).of_eq
    (fun t => rfl)

end DomainTheory.NeighbourhoodSystems
