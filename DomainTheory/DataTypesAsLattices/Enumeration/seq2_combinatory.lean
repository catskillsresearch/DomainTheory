/-ai
If x and y are combinatory, then the binary sequence constructor of x and y is combinatory.

The conditional of y against predecessor of zero is combinatory, and so is its composition on the left with S(K ·) and on the right with predecessor. The outer combination of S(K(cond x)) with that result is combinatory, as is the identity S K K. Their application under S is combinatory, and the SK equation for the binary sequence constructor identifies it with seq2 of x and y.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2_eq_SK

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem seq2_combinatory {x y : Pomega}
    (hx : IsCombinatory x) (hy : IsCombinatory y) :
    IsCombinatory (seq2 x y) := by
  have hyb : IsCombinatory (funOf (funOf condC y) (funOf predC zeroC)) :=
    .app (.app .cond hy) (.app .pred .zero)
  have hinter : IsCombinatory
      (funOf (funOf Scomb (funOf Kcomb
          (funOf (funOf condC y) (funOf predC zeroC)))) predC) :=
    .app (.app .S (.app .K hyb)) .pred
  have hF : IsCombinatory
      (funOf (funOf Scomb (funOf Kcomb (funOf condC x)))
        (funOf (funOf Scomb
            (funOf Kcomb (funOf (funOf condC y) (funOf predC zeroC))))
          predC)) :=
    .app (.app .S (.app .K (.app .cond hx))) hinter
  have hI : IsCombinatory (funOf (funOf Scomb Kcomb) Kcomb) :=
    .app (.app .S .K) .K
  have h := IsCombinatory.app (IsCombinatory.app IsCombinatory.S hF) hI
  simpa [seq2_eq_SK x y] using h

end DomainTheory.DataTypesAsLattices
