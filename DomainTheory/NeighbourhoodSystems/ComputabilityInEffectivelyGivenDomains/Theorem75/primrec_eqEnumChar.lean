module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.subChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.primrec_subChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.primrec_trivialChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.eqEnumChar

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

theorem primrec_eqEnumChar (gN incl0 incl1 eq1 : ℕ → ℕ) (hgNp : Nat.Primrec gN)
    (hincl0p : Nat.Primrec incl0) (hincl1p : Nat.Primrec incl1) (heq1p : Nat.Primrec eq1) :
    Nat.Primrec (fun t => eqEnumChar P₁ gN incl0 incl1 eq1 t.unpair.1 t.unpair.2) := by
  have ha := primrec_isOne.comp (hgNp.comp Nat.Primrec.left)
  have hb := primrec_isOne.comp (hgNp.comp Nat.Primrec.right)
  have hsubab : Nat.Primrec (fun t => subChar P₁ incl0 incl1 t.unpair.1 t.unpair.2) :=
    primrec_subChar P₁ incl0 incl1 hincl0p hincl1p
  have hsubba : Nat.Primrec (fun t => subChar P₁ incl0 incl1 t.unpair.2 t.unpair.1) :=
    ((primrec_subChar P₁ incl0 incl1 hincl0p hincl1p).comp
      (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq (fun t => by
        show subChar P₁ incl0 incl1 (Nat.pair t.unpair.2 t.unpair.1).unpair.1
          (Nat.pair t.unpair.2 t.unpair.1).unpair.2 = _
        rw [unpair_pair_fst, unpair_pair_snd])
  have htriva := (primrec_trivialChar P₁ eq1 heq1p).comp Nat.Primrec.left
  have htrivb := (primrec_trivialChar P₁ eq1 heq1p).comp Nat.Primrec.right
  have hbothcons := primrec_selectFn hsubab hsubba (Nat.Primrec.const 0)
  have hacons := primrec_selectFn hb hbothcons htriva
  have hanot := primrec_selectFn hb htrivb (Nat.Primrec.const 1)
  exact (primrec_selectFn ha hacons hanot).of_eq (fun _ => rfl)

end DomainTheory.NeighbourhoodSystems
