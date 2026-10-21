/-ai
Application of a seven-way sum to the injection of x at tag 1 is the injection at tag 1 of the application of the second summand to x.

Rewrite by the application equation, the body, the zero and one clauses of tagged injection, the predecessor of a successor numeral, the double conditional at one, and the double conditional at zero.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_app
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_one

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem plus7_app_tag1 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 1 x) = tagInj 1 (funOf a1 x) := by
  rw [plus7_app, plus7Body, tagInj_zero, tagInj_one, predSet_ofNat_succ,
    dcondSet_ofNat_one, dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
