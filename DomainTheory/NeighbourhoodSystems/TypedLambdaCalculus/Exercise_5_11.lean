module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.diagMap

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DiagMap

/-- Scott's Exercise 5.11: diagonal stack of a constant element, and componentwise
application of a stack of maps (stack combinators live in the infinite-product peer). -/
theorem example_511 :
    (∀ {α : Type*} (V : NeighborhoodSystem α) (x : V.Element) (n : ℕ),
      component ((diag V).toElementMap x) n = x) ∧
    (∀ {α : Type*} (V : NeighborhoodSystem α) (x : V.Element) (n : ℕ)
      (s : (iterSys (funSpace V V)).Element),
      component ((mapMap V).toElementMap (pair s x)) n =
        (toApproxMap (component s n)).toElementMap x) :=
  ⟨@component_diag, fun V x n s => component_map V x n s⟩

