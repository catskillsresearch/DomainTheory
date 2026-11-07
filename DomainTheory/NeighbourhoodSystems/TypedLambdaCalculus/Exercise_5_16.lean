module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.seqNegMerge

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap BitDom SeqDom SeqNegMerge

/-- Scott's Exercise 5.16: negation is an involution, merge on the diagonal is doubling,
and the Thue–Morse stream is cube-free. -/
theorem example_516 :
    (∀ x : C.Element, negMap.toElementMap (negMap.toElementMap x) = x) ∧
    (∀ x : C.Element, mergeMap.toElementMap (pair x x) = dMap.toElementMap x) ∧
    (∀ u a : Str, a ≠ [] → ¬ strBot (u ++ a ++ a ++ a) ≤ tElt) :=
  ⟨negMap_negMap, mergeMap_diag, tElt_cube_free⟩

