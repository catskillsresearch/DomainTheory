module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.11).** Closures act as expansive maps. -/
theorem eq_5_11 {a b u x : Pomega} (ha : Closure a) (hb : Closure b) :
    funOf u x ⊆ funOf b (funOf u (funOf a x)) := by
  have hx : x ⊆ funOf a x := by
    have := funOf_monotone_left ha.out.1 x
    rwa [Icomb_app] at this
  have hy : funOf u (funOf a x) ⊆ funOf b (funOf u (funOf a x)) := by
    have := funOf_monotone_left hb.out.1 (funOf u (funOf a x))
    rwa [Icomb_app] at this
  exact subset_trans (funOf_monotone_right u hx) hy

end DomainTheory.DataTypesAsLattices
