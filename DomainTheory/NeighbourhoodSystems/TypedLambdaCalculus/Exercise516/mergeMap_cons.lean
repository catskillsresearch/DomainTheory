/-ai
For bits ε and δ and elements x and y of C, merging the pair of ε consed onto x and δ consed onto y equals ε consed onto δ consed onto the merge of the pair (x, y).

The approximable map given by merge after the pairing of cons ε on the first projection with cons δ on the second projection equals cons ε after cons δ after merge. Extension to pairs of finite shape elements reduces the two sides by composition, pairing, the projections, the cons clause on shape elements, the pair clause of merge, and the cons-cons clause of the interleaving value. Evaluating that map identity at the pair (x, y) and simplifying the projections gives the element equation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.mergeMap_pair
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516.prodMap_ext

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44 Exercise419

















variable {β : Type*}











































/-- **Exercise 5.16 (Scott 1981, PRG-19).** The defining recursion of `merge`:
`merge(εx, δy) = ε·δ·merge(x, y)` for all `x, y ∈ |C|` and bits `ε, δ`. -/
theorem mergeMap_cons (ε δ : Bool) (x y : C.Element) :
    mergeMap.toElementMap
        (pair ((consMap ε).toElementMap x) ((consMap δ).toElementMap y))
      = (consMap ε).toElementMap
          ((consMap δ).toElementMap (mergeMap.toElementMap (pair x y))) := by
  have key :
      mergeMap.comp (paired ((consMap ε).comp (proj₀ C C)) ((consMap δ).comp (proj₁ C C)))
        = ((consMap ε).comp (consMap δ)).comp mergeMap := by
    apply prodMap_ext
    intro b₀ σ b₁ τ
    simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
      fst_pair, snd_pair, consMap_shapeElem, mergeMap_pair, mergeElem, mergeVal_cons_cons]
  have hx := congrArg (fun m : ApproximableMap (prod C C) C => m.toElementMap (pair x y)) key
  simp only [toElementMap_comp, toElementMap_paired, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair] at hx
  exact hx

end DomainTheory.NeighbourhoodSystems.Exercise516
