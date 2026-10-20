module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.expand_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.expand_cons

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- The Thue–Morse bit-function: `tm n = ⊕(binary digits of n)`, the parity of the number of `1`s in
the binary expansion of `n` (Lambek's description). -/
def tm (n : ℕ) : Bool := (Nat.bits n).foldr xor false

end DomainTheory.NeighbourhoodSystems.Exercise516
