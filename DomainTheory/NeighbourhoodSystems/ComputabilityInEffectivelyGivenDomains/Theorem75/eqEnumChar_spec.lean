/-ai
That characteristic equals one if and only if the two enumerated neighbourhoods are equal.

If both codes are consistent, the characteristic is the conjunction of the two inclusions of step neighbourhoods, which is equality by antisymmetry. If only the first is consistent, equality with the whole space is the triviality test. If only the second is consistent, the same test read in the other order is the equality. If neither is consistent, both enumerations are the whole space.
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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.selectFn_isOne
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.subChar_spec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.trivialChar_spec
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum_pos
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Xenum_neg
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.selectFn_mul_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.eqEnumChar

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

theorem eqEnumChar_spec (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2)
    (hincl1 : ∀ s, incl1 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2)
    (heq1 : ∀ s, eq1 s = 1 ↔ P₁.X s.unpair.1 = P₁.X s.unpair.2) (a b : ℕ) :
    eqEnumChar P₁ gN incl0 incl1 eq1 a b = 1 ↔ Xenum P₀ P₁ gN a = Xenum P₀ P₁ gN b := by
  unfold eqEnumChar
  by_cases ha : gN a = 1
  · rw [selectFn_isOne, ite_eq_left ha, selectFn_isOne]
    have hanea := (hgN a).mp ha
    by_cases hb : gN b = 1
    · rw [ite_eq_left hb, Xenum_pos P₀ P₁ ha, Xenum_pos P₀ P₁ hb, selectFn_mul_iff,
        subChar_spec P₀ P₁ incl0 incl1 hincl0 hincl1 hanea b,
        subChar_spec P₀ P₁ incl0 incl1 hincl0 hincl1 ((hgN b).mp hb) a]
      exact ⟨fun ⟨h1, h2⟩ => Set.Subset.antisymm h1 h2, fun h => ⟨h.subset, h.superset⟩⟩
    · rw [ite_eq_right hb, Xenum_pos P₀ P₁ ha, Xenum_neg P₀ P₁ hb, trivialChar_spec P₀ P₁ eq1 heq1 a]
  · rw [selectFn_isOne, ite_eq_right ha, selectFn_isOne]
    by_cases hb : gN b = 1
    · rw [ite_eq_left hb, Xenum_neg P₀ P₁ ha, Xenum_pos P₀ P₁ hb, trivialChar_spec P₀ P₁ eq1 heq1 b]
      exact eq_comm
    · rw [ite_eq_right hb, Xenum_neg P₀ P₁ ha, Xenum_neg P₀ P₁ hb]
      exact iff_of_true rfl rfl

end DomainTheory.NeighbourhoodSystems
