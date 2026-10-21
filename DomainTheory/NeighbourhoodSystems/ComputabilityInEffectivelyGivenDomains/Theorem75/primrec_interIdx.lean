/-ai
If the consistency characteristic is primitive recursive, then the function sending a paired code to the intersection index of its two components is primitive recursive.

Compose the characteristic with the two projections. The inner selection of the append code against the left projection, and the outer selection of that result against the right projection, are primitive recursive and agree with the paired intersection index.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.primrec_appendCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interIdx

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

theorem primrec_interIdx (gN : ℕ → ℕ) (hgNp : Nat.Primrec gN) :
    Nat.Primrec (fun t => interIdx gN t.unpair.1 t.unpair.2) := by
  have hn := hgNp.comp Nat.Primrec.left
  have hm := hgNp.comp Nat.Primrec.right
  have hinner := primrec_selectFn (primrec_isOne.comp hm) primrec_appendCode Nat.Primrec.left
  exact (primrec_selectFn (primrec_isOne.comp hn) hinner Nat.Primrec.right).of_eq (fun _ => rfl)

end DomainTheory.NeighbourhoodSystems
