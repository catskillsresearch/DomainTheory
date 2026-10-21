/-ai
The k-fold iterate of the Thue–Morse substitution on the singleton string of false is the Thue–Morse prefix of length 2 to the power k.

Induction on k. The zero iterate holds by reflexivity. For a successor, the iterate steps, the inductive hypothesis and the substitution step on prefixes give the prefix of length twice 2 to the power k, which equals 2 to the power k + 1.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.expand_tmList

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419













/-- **The bridge.** The `k`-fold morphism iterate of `[0]` is the Thue–Morse parity prefix of length
`2ᵏ`: `expandᵏ[0] = tmList (2ᵏ)`. -/
theorem expand_iterate_eq (k : ℕ) : (expand^[k] [false] : Str) = tmList (2 ^ k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, expand_tmList, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]

end DomainTheory.NeighbourhoodSystems.Exercise516
