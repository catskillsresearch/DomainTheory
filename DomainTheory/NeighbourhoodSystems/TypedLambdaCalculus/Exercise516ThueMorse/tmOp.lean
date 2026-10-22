module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.expand_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.expand_cons

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

/-- **Exercise 5.16 (the operator `Φ`).** `Φ(x) = 0·merge(neg x, tail x)` as an approximable map. -/
def tmOp : ApproximableMap C C :=
  (consMap false).comp (mergeMap.comp (paired negMap tailMap))

end DomainTheory.NeighbourhoodSystems.Exercise516
