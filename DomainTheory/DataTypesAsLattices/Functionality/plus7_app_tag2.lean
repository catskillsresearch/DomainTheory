/-ai
Application of a seven-way sum to the injection of x at tag 2 is the injection at tag 2 of the application of the third summand to x.

Rewrite by the application equation, the body, the zero and one clauses of tagged injection, the predecessor of a successor numeral, the double conditional at a successor, the predecessor of a successor numeral again, the double conditional at one, and the double conditional at zero.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_app
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_one

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem plus7_app_tag2 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 2 x) = tagInj 2 (funOf a2 x) := by
  rw [plus7_app, plus7Body, tagInj_zero, tagInj_one, predSet_ofNat_succ,
    dcondSet_ofNat_succ, predSet_ofNat_succ, dcondSet_ofNat_one,
    dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
