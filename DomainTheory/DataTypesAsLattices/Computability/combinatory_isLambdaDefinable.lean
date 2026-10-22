/-ai
Every combinatory element of Pω is the interpretation of a λ-term. This is the converse of Theorem 2.4.

Induct on the combinatory derivation. Zero is the zero term. Successor, predecessor, conditional, K, and S are the corresponding abstractions, and simplifying their interpretations recovers the combinators. An application is the application of the two witnessing terms.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- Combinatory elements are LAMBDA-definable (converse of Theorem 2.4). -/
theorem combinatory_isLambdaDefinable {u : Pomega} (hu : IsCombinatory u) :
    IsLambdaDefinable u := by
  induction hu with
  | zero => exact ⟨.zero, rfl⟩
  | suc =>
    refine ⟨.lam 0 (.succ (.var 0)), ?_⟩
    simp [interp, sucC, envSet, Function.update]
  | pred =>
    refine ⟨.lam 0 (.pred (.var 0)), ?_⟩
    simp [interp, predC, envSet, Function.update]
  | cond =>
    refine ⟨.lam 0 (.lam 1 (.lam 2
        (.cond (.var 2) (.var 0) (.var 1)))), ?_⟩
    simp [interp, condC, envSet, Function.update]
  | K =>
    refine ⟨.lam 0 (.lam 1 (.var 0)), ?_⟩
    simp [interp, Kcomb, envSet, Function.update]
  | S =>
    refine ⟨.lam 0 (.lam 1 (.lam 2
        (.app (.app (.var 0) (.var 2)) (.app (.var 1) (.var 2))))), ?_⟩
    simp [interp, Scomb, envSet, Function.update]
  | app _ _ iu iv =>
    obtain ⟨t, ht⟩ := iu
    obtain ⟨s, hs⟩ := iv
    exact ⟨.app t s, by simp [interp, ht, hs]⟩

end DomainTheory.DataTypesAsLattices
