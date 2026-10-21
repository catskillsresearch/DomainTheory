/-ai
A state lies in the epsilon-closure of a set of states of the concatenation automaton if and only if it already lies in the set, or the set contains some left accepting state and the state is a right copy of a start state of the second automaton.

In the forward direction, induct on the closure. A base member lies in the set. A further epsilon step leaves a left state only toward a right start state, and only from an accepting left state; a right state has no epsilon step, and a state added by an earlier crossing is already a right state, so it cannot be the source of another crossing. Conversely, members of the set lie in the closure, and a right start state is reached by one epsilon step from a left accepting state already in the closure.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.EpsilonNFA
import all Mathlib.Computability.EpsilonNFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability
open Sum Set

variable {σ₁ σ₂ : Type}


variable (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂)


/-- ε-closure: the only ε-edges go from an `inl`-accept state to `inr`-start states, so the closure
of `T` adds `inr '' M₂.start` exactly when `T` already contains some `inl`-accept state. -/
theorem catEps_mem_εClosure_iff (T : Set (σ₁ ⊕ σ₂)) (s : σ₁ ⊕ σ₂) :
    s ∈ (catEps M₁ M₂).εClosure T ↔
      s ∈ T ∨ ((∃ q ∈ M₁.accept, (inl q : σ₁ ⊕ σ₂) ∈ T) ∧ s ∈ inr '' M₂.start) := by
  constructor
  · intro h
    induction h using εNFA.εClosure_induction with
    | base x hx => exact Or.inl hx
    | step x y hyx _hclos ih =>
      -- a `none`-step `x → y`; nonempty only when `x = inl q`, `q ∈ M₁.accept`, `y ∈ inr '' start`
      cases x with
      | inl q =>
        rcases ih with hT | ⟨_, hmem⟩
        · simp only [catEps_step_inl_none, mem_ofPred_eq] at hyx
          exact Or.inr ⟨⟨q, hyx.1, hT⟩, hyx.2⟩
        · obtain ⟨w, _, hw⟩ := hmem; exact absurd hw.symm (by simp)
      | inr q => simp only [catEps_step_inr_none] at hyx; exact absurd hyx (by simp)
  · rintro (hs | ⟨⟨q, hq, hqT⟩, hs⟩)
    · exact (catEps M₁ M₂).subset_εClosure T hs
    · obtain ⟨t, ht, rfl⟩ := hs
      have hbase : (inl q : σ₁ ⊕ σ₂) ∈ (catEps M₁ M₂).εClosure T :=
        (catEps M₁ M₂).subset_εClosure T hqT
      refine (catEps M₁ M₂).mem_εClosure_of_mem_step ?_ hbase
      simp only [catEps_step_inl_none, mem_ofPred_eq]
      exact ⟨hq, t, ht, rfl⟩

end Exercise722
end DomainTheory.NeighbourhoodSystems
