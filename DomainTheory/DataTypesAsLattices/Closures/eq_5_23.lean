/-ai
Scott 1976, (5.23). The boxed sum of closures is a closure, so a value typed by the closure combinator is closed under boxed sum.

The typing hypotheses convert to closure hypotheses, the sum theorem produces a closure, and that closure converts back to a typing.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_4_plus
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5_universe

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.23).** Boxed sum of closures is a closure, so the map
is typed on `V`. -/
theorem eq_5_23 {a b : Pomega} (ha : typed a Vcomb) (hb : typed b Vcomb) :
    typed (boxPlus a b) Vcomb :=
  (theorem_5_5_universe.2 (boxPlus a b)).mp
    (theorem_5_4_plus ((theorem_5_5_universe.2 a).mpr ha)
      ((theorem_5_5_universe.2 b).mpr hb))

end DomainTheory.DataTypesAsLattices
