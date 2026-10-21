/-ai
A neighbourhood of C contained in the shape of (b, σ) is itself the shape of some tagged string (b', σ'), and the shape element of (b, σ) lies below the shape element of (b', σ').

Split the neighbourhood into a cone or a singleton. The cone is the partial shape of its string, and the singleton is the total shape of its string. In each case the given containment is the principal order of the two shape elements.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.flip_flip
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.double_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailMap_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.tailMap_strElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.negMap_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.negMap_strElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.dMap_strBot
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.dMap_strElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.shape
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.memC_shape
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.shapeElem
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.shapeElem_true
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.shapeElem_false
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeVal_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeVal_cons_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeVal_cons_cons

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

variable {β : Type*}

theorem shape_refine {b : Bool} {σ : Str} {P : Set Str} (hP : memC P) (hsub : P ⊆ shape b σ) :
    ∃ (b' : Bool) (σ' : Str), P = shape b' σ' ∧ shapeElem b σ ≤ shapeElem b' σ' := by
  rcases hP with ⟨ρ, rfl⟩ | ⟨ρ, rfl⟩
  · exact ⟨false, ρ, rfl, (C.principal_le_iff (memC_shape b σ) (memC_shape false ρ)).mpr hsub⟩
  · exact ⟨true, ρ, rfl, (C.principal_le_iff (memC_shape b σ) (memC_shape true ρ)).mpr hsub⟩

end DomainTheory.NeighbourhoodSystems.Exercise516
