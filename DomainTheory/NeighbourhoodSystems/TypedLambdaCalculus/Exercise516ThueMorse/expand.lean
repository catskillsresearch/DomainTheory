/-ai
The Thue–Morse substitution acts letterwise. The empty string is sent to the empty string, and a bit b followed by σ is sent to b, then the negation of b, then the substitution of σ.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bits

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- The Thue–Morse substitution applied letterwise: each bit `b` is replaced by `b (¬b)`. -/
def expand : Str → Str
  | [] => []
  | b :: σ => b :: (!b) :: expand σ

end DomainTheory.NeighbourhoodSystems.Exercise516
