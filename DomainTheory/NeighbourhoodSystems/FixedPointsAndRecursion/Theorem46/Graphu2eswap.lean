/-ai
A pair related by the graph of two models of Peano's axioms is related in the opposite order by the graph of the models with their roles exchanged.

The proof is induction on the generating relation. The pair of zeros is symmetric. A successor step swaps to a successor step of the swapped relation.
ai-/
module

public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

universe u v


namespace PeanoModel

variable {M : Type u} {N : Type v}


/-- The construction is symmetric in the two models: `Graph P Q m n` swaps to `Graph Q P n m`.
(This is why the relation is one-one in *both* directions, as Scott notes: "the rôles of `N` and
`M` are completely symmetric".) -/
theorem Graph.swap {P : PeanoModel M} {Q : PeanoModel N} {m : M} {n : N}
    (h : Graph P Q m n) : Graph Q P n m := by
  induction h with
  | base => exact Graph.base
  | step _ ih => exact Graph.step ih

end PeanoModel
end DomainTheory.NeighbourhoodSystems
