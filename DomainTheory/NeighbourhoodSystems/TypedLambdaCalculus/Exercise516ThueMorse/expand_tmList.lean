/-ai
Applying the Thue–Morse substitution to the length-m prefix yields the length-2m prefix.

Induction on m. The zero case holds by reflexivity. For a successor, the prefix of length 2(m + 1) equals the prefix of length 2m followed by the bit at m and its negation: rewrite the length as two successors, apply the successor law twice, the odd and even recurrences, and associativity, and the equation holds by reflexivity. The successor law, the append law, the inductive hypothesis, that identification, and the cons and nil clauses of the substitution then match the two sides.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.expand_append
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tm_two_mul
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tm_two_mul_add_one
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tmList_succ

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419


/-- **The morphism step on prefixes.** `expand (tmList m) = tmList (2m)`: applying the Thue–Morse
morphism to a length-`m` prefix yields the length-`2m` prefix — this is exactly the even/odd parity
recurrence in disguise. -/
theorem expand_tmList (m : ℕ) : expand (tmList m) = tmList (2 * m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have key : tmList (2 * (m + 1)) = tmList (2 * m) ++ [tm m, !tm m] := by
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, tmList_succ, tmList_succ,
        tm_two_mul_add_one, tm_two_mul, List.append_assoc]
      rfl
    rw [tmList_succ, expand_append, ih, key, expand_cons, expand_nil]

end DomainTheory.NeighbourhoodSystems.Exercise516
