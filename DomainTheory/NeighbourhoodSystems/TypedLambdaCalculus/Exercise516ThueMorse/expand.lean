module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- The Thue–Morse substitution applied letterwise: each bit `b` is replaced by `b (¬b)`. -/
def expand : Str → Str
  | [] => []
  | b :: σ => b :: (!b) :: expand σ

end DomainTheory.NeighbourhoodSystems.Exercise516
