/-ai
The Thue–Morse substitution distributes over concatenation: the substitution of σ followed by τ equals the substitution of σ followed by the substitution of τ.

Induction on σ. The empty case holds by reflexivity. A cons simplifies by the inductive hypothesis.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419


/-- `expand` distributes over append (it is a monoid morphism `Σ* → Σ*`). -/
theorem expand_append (σ τ : Str) : expand (σ ++ τ) = expand σ ++ expand τ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => simp [ih]

end DomainTheory.NeighbourhoodSystems.Exercise516
