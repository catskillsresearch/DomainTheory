/-ai
The value of Φ on the partial element given by a string σ is the partial element whose string is false followed by the first component of the merge of the flipped string with the tail, both carrying a false second component.

Unfold Φ. Rewrite by the composition law twice, the pairing law, the action of negation and of the tail on partial elements, the definitional identifications of those partial elements with shape elements headed by false, the merge of a pair and of an element, the vanishing of the second merge component, the shape of false, and cons on a partial element.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516
public import Mathlib.Data.Nat.Bits
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse.mergeVal_snd_false

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419


/-- The value of `Φ` on a partial element `σ⊥` is `(0 · weave σ)⊥`, the leading `0` prepended to the
interleaving of `(flip σ)⊥` and `(tail σ)⊥`. -/
theorem tmOp_strBot (σ : Str) :
    tmOp.toElementMap (strBot σ)
      = strBot (false :: (mergeVal (flip σ) false σ.tail false).1) := by
  unfold tmOp
  rw [toElementMap_comp, toElementMap_comp, toElementMap_paired, negMap_strBot, tailMap_strBot,
    show (strBot (flip σ)) = shapeElem false (flip σ) from rfl,
    show (strBot σ.tail) = shapeElem false σ.tail from rfl, mergeMap_pair, mergeElem,
    mergeVal_snd_false, shapeElem_false, consMap_strBot]

end DomainTheory.NeighbourhoodSystems.Exercise516
