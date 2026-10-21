/-ai
Application of a seven-way sum to the injection of x at tag 5 is the injection at tag 5 of the application of the sixth summand to x.

Rewrite by the application equation, the body, the zero and one clauses of tagged injection, the double conditional at a successor, the predecessor of a successor numeral, the double conditional at a successor, the predecessor of a successor numeral, the double conditional at a successor, three iterations of the predecessor sending the numeral 5 to the numeral 2, the double conditional at a successor, four iterations of the predecessor sending the numeral 5 to the numeral 1, the double conditional at one, iteration of the predecessor sending the numeral 5 to zero, and the double conditional at zero.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_ofNat
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_self
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_app
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_one

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem plus7_app_tag5 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 5 x) = tagInj 5 (funOf a5 x) := by
  rw [plus7_app, plus7Body, tagInj_zero, tagInj_one, dcondSet_ofNat_succ,
    predSet_ofNat_succ, dcondSet_ofNat_succ, predSet_ofNat_succ,
    dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 2),
    dcondSet_ofNat_succ, predSet_iterate_ofNat (k := 4) (i := 1),
    dcondSet_ofNat_one, predSet_iterate_self, dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
