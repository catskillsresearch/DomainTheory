module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.funOf_top
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem plus7_app_top (a0 a1 a2 a3 a4 a5 a6 : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) topElem = topElem := by
  rw [plus7_app, plus7Body, funOf_top, dcondSet_top]

end DomainTheory.DataTypesAsLattices
