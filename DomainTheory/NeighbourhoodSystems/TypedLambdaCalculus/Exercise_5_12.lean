module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.whileMap

@[expose] public section

open DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap
open DomainTheory.NeighbourhoodSystems.WhileMap
open DomainTheory.NeighbourhoodSystems.Cond (cond TD)
open Truth

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
      p.toElementMap x = Truth.botElt →
        (whileMap V p f).toElementMap x = V.bot) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (p : ApproximableMap V TD)
      (f : ApproximableMap V V) {x : V.Element},
      p.toElementMap x = Truth.falseElt →
        (whileMap V p f).toElementMap x = x) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (p : ApproximableMap V TD)
      (f : ApproximableMap V V) {x : V.Element},
      p.toElementMap x = Truth.trueElt →
        (whileMap V p f).toElementMap x =
          (whileMap V p f).toElementMap (f.toElementMap x)) :=
  ⟨@whileMap_rec, @whileMap_bot, @whileMap_false, @whileMap_true⟩

