/-ai
Scott's Thue–Morse element t is the least fixed point of the operator sending x to 0 consed onto the merge of the negation of x with the tail of x.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.expand_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.expand_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tmOp
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tm_zero
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.tmList_zero

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- **Exercise 5.16 (Scott 1981, PRG-19).** Scott's Thue–Morse element `t = 0·merge(neg t, tail t)`,
the least fixed point of `Φ`. -/
def tElt : C.Element := tmOp.fixElement

end DomainTheory.NeighbourhoodSystems.Exercise516
