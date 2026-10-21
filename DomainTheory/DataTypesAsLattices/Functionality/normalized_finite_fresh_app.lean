/-ai
Application of the graph of application of e p, at the union of the iterate Z m (e p) (e q) with the singleton pair of max(p, q) + 1 and m, equals the next iterate Z (m + 1) (e p) (e q).

Rewrite by the normalized finite application and by the fresh-union clause for application of e, using that the fresh index is strictly above p. The two sides are then identical.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
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
