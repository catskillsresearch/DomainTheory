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

/-- A `{0,1}` left-fold `AND` of `isOne ∘ g` over a list, started from `a ∈ {0,1}`. -/
theorem andFoldl_eq_one_iff (g : ℕ → ℕ) :
    ∀ (el : List ℕ) (a : ℕ), a ≤ 1 →
      (List.foldl (fun acc x => selectFn acc (isOne (g x)) 0) a el = 1 ↔
        a = 1 ∧ ∀ e ∈ el, g e = 1)
  | [], a, _ => by simp
  | e :: el, a, ha => by
    rw [List.foldl_cons]
    have hstep : selectFn a (isOne (g e)) 0 ≤ 1 := by
      rcases (show a = 0 ∨ a = 1 by omega) with h | h <;> subst h
      · rw [selectFn_zero]; exact Nat.zero_le 1
      · rw [selectFn_one]; exact isOne_le_one _
    rw [andFoldl_eq_one_iff g el _ hstep]
    rcases (show a = 0 ∨ a = 1 by omega) with h | h <;> subst h
    · rw [selectFn_zero]; simp
    · rw [selectFn_one, List.forall_mem_cons, isOne_eq_one_iff]
      constructor
      · rintro ⟨hge, hall⟩; exact ⟨rfl, hge, hall⟩
      · rintro ⟨_, hge, hall⟩; exact ⟨hge, hall⟩

end DomainTheory.NeighbourhoodSystems
