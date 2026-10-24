module

public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.PeanoModel
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46.Graph

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
