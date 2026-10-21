/-ai
For fixed u and x, the map sending y to the application of u to the pair sequence of x and y is Scott-continuous.

Theorem 1.3 applies to continuity of application of u and to right continuity of the pair sequence at x.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem curry_body_isScottContinuous_y (u x : Pomega) :
    IsScottContinuous (fun y => funOf u (pairSeq x y)) :=
  theorem_1_3 (funOf_isScottContinuous u) (pairSeq_isScottContinuous_right x)

end DomainTheory.DataTypesAsLattices
