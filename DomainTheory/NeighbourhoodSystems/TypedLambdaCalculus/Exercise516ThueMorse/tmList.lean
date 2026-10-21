/-ai
The length-n Thue–Morse prefix is the list of bits at 0, 1, …, n − 1, obtained by mapping the bit function along the range of length n.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.expand_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.expand_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tm
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tm_zero

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- The length-`n` Thue–Morse prefix `[tm 0, tm 1, …, tm (n-1)]`. -/
def tmList (n : ℕ) : Str := (List.range n).map tm

end DomainTheory.NeighbourhoodSystems.Exercise516
