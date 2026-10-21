/-ai
If the consistency characteristic is primitive recursive, then the function sending a paired code to the consistency characteristic of its two components is primitive recursive.

Compose the characteristic with the two projections and with the append code. The inner selection on the second component, and then the outer selection on the first, are primitive recursive and agree with the paired consistency characteristic.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.consPairChar

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

theorem primrec_consPairChar (gN : ℕ → ℕ) (hgNp : Nat.Primrec gN) :
    Nat.Primrec (fun t => consPairChar gN t.unpair.1 t.unpair.2) := by
  have hn := hgNp.comp Nat.Primrec.left
  have hm := hgNp.comp Nat.Primrec.right
  have happ := hgNp.comp primrec_appendCode
  have hinner := primrec_selectFn (primrec_isOne.comp hm) happ (Nat.Primrec.const 1)
  exact (primrec_selectFn (primrec_isOne.comp hn) hinner (Nat.Primrec.const 1)).of_eq (fun _ => rfl)

end DomainTheory.NeighbourhoodSystems
