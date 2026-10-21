/-ai
Scott's negation on C is the approximable map built by the head-test combinator so that the partial element of σ is sent to the partial element of the bit-flipped string, and the total element of σ is sent to the total element of the bit-flipped string.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_flip
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailMap_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailMap_strElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.neg_hcone
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.neg_hsing

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

variable {β : Type*}

/-- **Exercise 5.16 — `neg : C → C`.** The closed-form solution of Scott's recursion, built with
`liftC`: `neg(σ⊥) = (flip σ)⊥` and `neg(σ) = flip σ`. -/
def negMap : ApproximableMap C C :=
  liftC C (fun σ => strBot (flip σ)) (fun σ => strElem (flip σ)) neg_hcone neg_hsing

end DomainTheory.NeighbourhoodSystems.Exercise516
