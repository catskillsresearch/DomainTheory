/-ai
The tail of a stack is the sequence of its components from index one onward.

The tail is a composite, unfolding applies the product isomorphism, that isomorphism is the pair of the zeroth component and the shifted sequence, and the second projection of the pair is the shifted sequence.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.unfold
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.iterProdIso_apply
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.tail
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.head_apply

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem tail_apply (z : (iterSys V).Element) :
    (tail V).toElementMap z = ofSeq (fun n => component z (n + 1)) := by
  rw [tail, toElementMap_comp, unfold, toElementMap_ofIso, toElementMap_proj₁,
    iterProdIso_apply, snd_pair]

end DomainTheory.NeighbourhoodSystems.Exercise511
