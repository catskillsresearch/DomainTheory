/-ai
Every iterate of the Thue–Morse substitution starting from the singleton string of false begins with the bit false.

Induction on the iteration count. The zero iterate is that singleton. A successor applies the substitution to a string headed by false, and the cons clause yields false followed by true followed by the substitution of the tail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419


/-- Every iterate of `expand` from `[0]` starts with `0` (so `Φ` keeps acting as `expand`). -/
theorem iterate_expand_cons (k : ℕ) : ∃ ρ, (expand^[k] [false] : Str) = false :: ρ := by
  induction k with
  | zero => exact ⟨[], rfl⟩
  | succ k ih =>
    obtain ⟨ρ, hρ⟩ := ih
    exact ⟨true :: expand ρ, by rw [Function.iterate_succ_apply', hρ]; rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise516
