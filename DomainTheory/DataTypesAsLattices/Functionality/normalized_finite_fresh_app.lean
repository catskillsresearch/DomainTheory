
module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.Z
public import DomainTheory.DataTypesAsLattices.Functionality.funOf_e_union_fresh
public import DomainTheory.DataTypesAsLattices.Functionality.normalized_finite_app

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem normalized_finite_fresh_app (p q m : ℕ) :
    funOf (graph (fun y => funOf (e p) y))
        (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) =
      Z (m + 1) (e p) (e q) := by
  rw [normalized_finite_app,
    funOf_e_union_fresh p (max p q + 1) m _
      (Nat.lt_succ_of_le (Nat.le_max_left p q))]
  rfl

end DomainTheory.DataTypesAsLattices
