/-ai
Application is monotone in both arguments: if a set of codes grows and the argument set grows, the set of outputs grows.

A witnessing list for an output has its entries in the smaller argument, hence in the larger one, and its tag in the smaller set of codes, hence in the larger one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513


/-- **`Fun` is monotone in both arguments jointly.** Needed to check the `mono` axiom of the
neighbourhood-level approximable map built from `Fun` (Exercise 7.23). -/
theorem Fun_mono {u u' x x' : Set ℕ} (hu : u ⊆ u') (hx : x ⊆ x') : Fun u x ⊆ Fun u' x' := by
  rintro m ⟨ns, hns, htag⟩
  exact ⟨ns, fun n hn => hx (hns n hn), hu htag⟩

end DomainTheory.NeighbourhoodSystems.Exercise514
