module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funListOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.decodeList_encodeList
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum_pos
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum_nonempty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum_inter_eq
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.consPairChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.consPairChar_spec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.primrec_consPairChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.primrec_interIdx
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interEqChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interEqChar_spec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.primrec_interEqChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.exists_funListOf

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- **The function-space presentation.** Built from explicit characteristic functions for the
component presentations' relations (`gN` = function-space consistency, `incl0`/`incl1` = inclusion,
`eq1` = equality), so it is choice-free given those concrete functions. -/
def funPresentation (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ P₁.X s.unpair.1 = P₁.X s.unpair.2) (heq1p : Nat.Primrec eq1) :
    ComputablePresentation (funSpace V₀ V₁) where
  X := Xenum P₀ P₁ gN
  mem_X := Xenum_mem P₀ P₁ gN hgN
  surj := by
    rintro W ⟨⟨L, hL, rfl⟩, hne⟩
    obtain ⟨el, hel⟩ := exists_funListOf P₀ P₁ hL
    have hc : gN (encodeList el) = 1 := by rw [hgN, decodeList_encodeList, hel]; exact hne
    exact ⟨encodeList el, by rw [Xenum_pos P₀ P₁ hc, decodeList_encodeList, hel]⟩
  interEq_computable :=
    ⟨fun t => interEqChar P₁ gN incl0 incl1 eq1 t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2,
      primrec_interEqChar P₁ gN incl0 incl1 eq1 hgNp hincl0p hincl1p heq1p,
      fun t => (interEqChar_spec P₀ P₁ gN incl0 incl1 eq1 hgN hincl0 hincl1 heq1
        t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2).symm⟩
  cons_computable :=
    ⟨fun t => consPairChar gN t.unpair.1 t.unpair.2, primrec_consPairChar gN hgNp,
      fun t => (consPairChar_spec P₀ P₁ gN hgN t.unpair.1 t.unpair.2).symm⟩
  inter := interIdx gN
  inter_primrec := primrec_interIdx gN hgNp
  inter_spec := by
    intro n m h
    obtain ⟨k, hk⟩ := h
    exact Xenum_inter_eq P₀ P₁ gN hgN n m ((Xenum_nonempty P₀ P₁ gN hgN k).mono hk)
  masterIdx := 0
  masterIdx_spec := by
    show Xenum P₀ P₁ gN 0 = Set.univ
    unfold Xenum
    rw [decodeList_zero]
    simp only [funListOf, List.map_nil, stepFun_nil, ite_self]

end DomainTheory.NeighbourhoodSystems
