module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_flip
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailSing
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tail_hcone
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tail_hsing
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailMap
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailMap_strBot

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

variable {β : Type*}

@[simp] theorem tailMap_strElem (σ : Str) :
    tailMap.toElementMap (strElem σ) = tailSing σ :=
  liftC_strElem C (fun σ => strBot σ.tail) tailSing tail_hcone tail_hsing σ

end DomainTheory.NeighbourhoodSystems.Exercise516
