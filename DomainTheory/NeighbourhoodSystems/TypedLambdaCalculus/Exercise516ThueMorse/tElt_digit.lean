/-ai
The n-th digit of t is the Thue–Morse bit at n: the partial element of the length-n prefix followed by that bit lies below t.

The prefix of length n + 1 lies below t, and the successor law rewrites it as the length-n prefix followed by the bit at n.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
import all Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tmList_succ
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tmList_le_tElt

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419
















/-- **Property (a), digit form.** The `n`-th digit of `t` is `tm n` (the parity of the binary digits
of `n`): the length-`(n+1)` prefix of `t` is `tmList n ++ [tm n]`. -/
theorem tElt_digit (n : ℕ) : strBot (tmList n ++ [tm n]) ≤ tElt := by
  have h := tmList_le_tElt (n + 1)
  rwa [tmList_succ] at h

end DomainTheory.NeighbourhoodSystems.Exercise516
