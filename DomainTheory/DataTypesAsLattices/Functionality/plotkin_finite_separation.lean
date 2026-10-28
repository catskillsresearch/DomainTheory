
module

public import DomainTheory.DataTypesAsLattices.Lambda.eq_2_9
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.Z
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ
public import DomainTheory.DataTypesAsLattices.Functionality.funOf_e_union_fresh
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem plotkin_finite_separation (p q m : ℕ) :
    Z m
        (graph (fun y => funOf (e p) y) ∪
          graph (sigmaJ (max p q + 1)))
        ((e q) ∪ {pair (max p q + 1) 0}) =
      Z m (e p) (e q) ∪ {pair (max p q + 1) m} := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Z, eq_2_9, ih]
      have hbeta :
          funOf (graph (fun y => funOf (e p) y))
              (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) =
            funOf (e p) (Z m (e p) (e q) ∪ {pair (max p q + 1) m}) :=
        beta (funOf.isScottContinuous (e p)) _
      rw [hbeta, funOf_e_union_fresh p (max p q + 1) m _
        (Nat.lt_succ_of_le (Nat.le_max_left p q)), sigmaJ.app,
        sigmaJ.union_fresh (fun k => Z.finite_no_tag p q m k)]
      rfl

end DomainTheory.DataTypesAsLattices
