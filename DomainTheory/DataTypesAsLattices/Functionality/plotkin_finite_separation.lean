
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_app
public import DomainTheory.DataTypesAsLattices.Functionality.Z_finite_no_tag
public import DomainTheory.DataTypesAsLattices.Functionality.funOf_e_union_fresh
public import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_union_fresh

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
        beta (funOf_isScottContinuous (e p)) _
      rw [hbeta, funOf_e_union_fresh p (max p q + 1) m _
        (Nat.lt_succ_of_le (Nat.le_max_left p q)), sigmaJ_app,
        sigmaJ_union_fresh (fun k => Z_finite_no_tag p q m k)]
      rfl

end DomainTheory.DataTypesAsLattices
