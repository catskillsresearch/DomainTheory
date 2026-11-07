module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.whileMap

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap WhileMap
open DomainTheory.NeighbourhoodSystems.Exercise326 (cond TD)

/-- Scott's Exercise 5.12: the while combinator as a least fixed point satisfying the
conditional recursion, with the three truth-value cases. -/
theorem example_512 :
    (∀ {α : Type*} (V : NeighborhoodSystem α) (p : ApproximableMap V TD)
      (f : ApproximableMap V V) (x : V.Element),
      (whileMap V p f).toElementMap x =
        (cond V).toElementMap
          (pair (p.toElementMap x)
            (pair ((whileMap V p f).toElementMap (f.toElementMap x)) x))) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (p : ApproximableMap V TD)
      (f : ApproximableMap V V) {x : V.Element},
      p.toElementMap x = Example23.botElt →
        (whileMap V p f).toElementMap x = V.bot) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (p : ApproximableMap V TD)
      (f : ApproximableMap V V) {x : V.Element},
      p.toElementMap x = Example23.falseElt →
        (whileMap V p f).toElementMap x = x) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (p : ApproximableMap V TD)
      (f : ApproximableMap V V) {x : V.Element},
      p.toElementMap x = Example23.trueElt →
        (whileMap V p f).toElementMap x =
          (whileMap V p f).toElementMap (f.toElementMap x)) :=
  ⟨@whileMap_rec, @whileMap_bot, @whileMap_false, @whileMap_true⟩

end DomainTheory.NeighbourhoodSystems
