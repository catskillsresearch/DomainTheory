module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_17

@[expose] public section


namespace DomainTheory.DataTypesAsLattices











theorem Vapply_eq_imp_idem {a : Pomega}
    (h : ∀ x, Vapply a x = funOf a x) (x : Pomega) :
    funOf a (funOf a x) = funOf a x := by
  have := eq_5_17 a x
  rwa [h (Vapply a x), h x] at this

end DomainTheory.DataTypesAsLattices
