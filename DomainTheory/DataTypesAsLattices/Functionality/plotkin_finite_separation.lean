/-ai
The m-fold iterate, under the union of the graph of application of e p with the graph of sigmaJ at max(p, q) + 1, of e q with the pair of that fresh index and zero adjoined, equals the plain iterate Z m (e p) (e q) with the pair of that index and m adjoined.

Induction on m. The zero case is reflexivity. At a successor, rewrite by the recursive clause of Z, by equation (2.9), and by the inductive hypothesis. β-conversion, using continuity of application of e p, replaces application of the graph by application of e p. The fresh-union clause for that application, with the index strictly above p, the application equation for sigmaJ, and the fresh-union equation for sigmaJ, using that the finite iterate carries no pair at the fresh index, make the two sides identical.
ai-/

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
