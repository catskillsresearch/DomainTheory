/-ai
The modified boolean closure applied to u equals the conditional of u on the singleton {0} and on ⊤ + 1.

The body of the closure is Scott continuous, so the β rule evaluates its graph at u as that conditional.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boool_map_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



































theorem boool_app (u : Pomega) :
    funOf boool u = condSet u (ofNat 0) (succSet topElem) :=
  beta boool_map_isScottContinuous u

end DomainTheory.DataTypesAsLattices
