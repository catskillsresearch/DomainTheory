/-ai
When the intersection of two enumerated neighbourhoods is nonempty, the enumeration at the intersection index equals that intersection.

Unfold the intersection index and rewrite the selection. If both characters equal one, both enumerations are the step neighbourhoods, the append code is consistent because that intersection is nonempty, and the enumeration of the append equals the intersection. If the second character is not one, the second enumeration is the whole space, and intersection on the right with the whole space is the first enumeration. If the first character is not one, the first enumeration is the whole space, and intersection on the left with the whole space is the second enumeration.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funListOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.appendCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.stepFun_funListOf_appendCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.selectFn_isOne
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum_pos
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum_neg
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interIdx

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- **`interIdx` codes the intersection** whenever it is non-empty (and the result is in the
enumeration). -/
theorem Xenum_inter_eq (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (n m : ℕ)
    (hne : (Xenum P₀ P₁ gN n ∩ Xenum P₀ P₁ gN m).Nonempty) :
    Xenum P₀ P₁ gN (interIdx gN n m) = Xenum P₀ P₁ gN n ∩ Xenum P₀ P₁ gN m := by
  unfold interIdx
  rw [selectFn_isOne]
  by_cases hn : gN n = 1
  · rw [ite_eq_left hn, selectFn_isOne]
    by_cases hm : gN m = 1
    · rw [ite_eq_left hm, Xenum_pos P₀ P₁ hn, Xenum_pos P₀ P₁ hm, ← stepFun_funListOf_appendCode P₀ P₁ n m]
      rw [Xenum_pos P₀ P₁ hn, Xenum_pos P₀ P₁ hm] at hne
      have hgne : gN (appendCode n m) = 1 :=
        (hgN _).mpr (by rw [stepFun_funListOf_appendCode P₀ P₁ n m]; exact hne)
      rw [Xenum_pos P₀ P₁ hgne]
    · rw [ite_eq_right hm, Xenum_neg P₀ P₁ hm, Set.inter_univ]
  · rw [ite_eq_right hn, Xenum_neg P₀ P₁ hn, Set.univ_inter]

end DomainTheory.NeighbourhoodSystems
