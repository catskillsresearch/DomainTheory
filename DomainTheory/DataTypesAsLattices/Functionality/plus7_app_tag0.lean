/-ai
Application of a seven-way sum to the injection of x at tag 0 is the injection at tag 0 of the application of the first summand to x.

Rewrite by the application equation, the body, the zero and one clauses of tagged injection, and the double conditional at the numeral zero.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_app
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_one

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem plus7_app_tag0 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 0 x) = tagInj 0 (funOf a0 x) := by
  rw [plus7_app, plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
