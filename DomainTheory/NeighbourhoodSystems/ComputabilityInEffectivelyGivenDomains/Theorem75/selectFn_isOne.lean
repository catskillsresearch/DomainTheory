module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- `selectFn` driven by `isOne` is a `Nat`-equality `if` (choice-free; `decEq` on `ℕ`). -/
theorem selectFn_isOne (v a b : ℕ) : selectFn (isOne v) a b = if v = 1 then a else b := by
  by_cases h : v = 1
  · rw [ite_eq_left h, h, (isOne_eq_one_iff 1).mpr rfl, selectFn_one]
  · rw [ite_eq_right h]
    have h0 : isOne v = 0 := by
      rcases (show isOne v = 0 ∨ isOne v = 1 from by have := isOne_le_one v; omega) with h0 | h1
      · exact h0
      · exact absurd ((isOne_eq_one_iff v).mp h1) h
    rw [h0, selectFn_zero]

end DomainTheory.NeighbourhoodSystems
