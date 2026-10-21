/-ai
The component of index n of the map combinator applied to a stack of functions and an element is the function of index n in the stack applied to the element.

The proof is by induction on the index, for an arbitrary stack. The zeroth component is the head, and the recursion for map together with the head-of-push law and the head computation returns the head function applied to the element. At a successor, the tail of the mapped stack is map applied to the tail of the function stack and the same element, by the recursion and the tail-of-push law, and the inductive hypothesis together with the component formula for the tail reads the next function.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.component_tail
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.head_push
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.tail_push
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise511.map_rec

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise511

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*} (V : NeighborhoodSystem α)


















/-- **Exercise 5.11 (Scott 1981, PRG-19).** The `n`-th component of `map(s, x)` is `(component s n)(x)`,
i.e. `map(⟨fₙ⟩, x) = ⟨fₙ(x)⟩ₙ`. -/
theorem component_map (x : V.Element) :
    ∀ (n : ℕ) (s : (iterSys (funSpace V V)).Element),
      component ((mapMap V).toElementMap (pair s x)) n =
        (toApproxMap (component s n)).toElementMap x := by
  intro n
  induction n with
  | zero =>
    intro s
    rw [← head_apply, map_rec, head_push, head_apply]
  | succ k ih =>
    intro s
    have ht : (tail V).toElementMap ((mapMap V).toElementMap (pair s x)) =
        (mapMap V).toElementMap (pair ((tail (funSpace V V)).toElementMap s) x) := by
      conv_lhs => rw [map_rec]
      rw [tail_push]
    rw [← component_tail, ht, ih, component_tail]

end DomainTheory.NeighbourhoodSystems.Exercise511
