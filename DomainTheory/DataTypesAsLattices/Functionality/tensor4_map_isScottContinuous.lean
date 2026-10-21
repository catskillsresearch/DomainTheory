/-ai
The map sending u to the four-way sequence of a, b, c, and d applied to the four components of u is Scott continuous.

Continuity of the four-way sequence is applied to four continuous arguments. Each argument is Theorem 1.3 applied to application of one factor and to left application at the corresponding numeral.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_comp_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem tensor4_map_isScottContinuous (a b c d : Pomega) :
    IsScottContinuous (fun u =>
      seq4 (funOf a (funOf u (ofNat 0)))
        (funOf b (funOf u (ofNat 1)))
        (funOf c (funOf u (ofNat 2)))
        (funOf d (funOf u (ofNat 3)))) :=
  seq4_comp_isScottContinuous
    (theorem_1_3 (funOf_isScottContinuous a) (funOf_isScottContinuous_left (ofNat 0)))
    (theorem_1_3 (funOf_isScottContinuous b) (funOf_isScottContinuous_left (ofNat 1)))
    (theorem_1_3 (funOf_isScottContinuous c) (funOf_isScottContinuous_left (ofNat 2)))
    (theorem_1_3 (funOf_isScottContinuous d) (funOf_isScottContinuous_left (ofNat 3)))

end DomainTheory.DataTypesAsLattices
