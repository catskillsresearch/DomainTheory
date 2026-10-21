/-ai
If the equality characteristic is primitive recursive, then the triviality characteristic is primitive recursive.

It is the fold of the primitive-recursive triviality step, with constant parameter 0, constant start 1, and the identity as the list code.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.trivialChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.primrec_trivStp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

theorem primrec_trivialChar (eq1 : ℕ → ℕ) (heq1p : Nat.Primrec eq1) :
    Nat.Primrec (trivialChar P₁ eq1) :=
  (primrec_foldCode (primrec_trivStp P₁ eq1 heq1p) (Nat.Primrec.const 0)
    (Nat.Primrec.const 1) primrec_id).of_eq (fun _ => rfl)

end DomainTheory.NeighbourhoodSystems
