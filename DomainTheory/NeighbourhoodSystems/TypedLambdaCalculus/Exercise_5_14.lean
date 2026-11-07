module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.setGraph

@[expose] public section

open DomainTheory.NeighbourhoodSystems

open SetGraph

/-- Scott's Exercise 5.14: `Fun` and `Graph` recover approximable set-maps and
dominate the identity on graphs. -/
theorem example_514 :
    (∀ u : Set ℕ, IsApprox (Fun u)) ∧
    (∀ {f : Set ℕ → Set ℕ}, IsApprox f → ∀ x : Set ℕ, Fun (Graph f) x = f x) ∧
    (∀ u : Set ℕ, u ⊆ Graph (Fun u)) :=
  ⟨Fun_isApprox, @Fun_Graph, id_le_Graph_Fun⟩

