module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.sSup_fixed_eq_sUnion
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_directed
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_sSup

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem retractBasis_sUnion {a : Pomega} (ha : Retract a)
    (x : Fixpoints (funOf a)) :
    (x : Pomega) = ⋃₀ (Subtype.val '' retractBasis a x) := by
  have h := retractBasis_sSup ha x
  have hsu := sSup_fixed_eq_sUnion (funOf_isScottContinuous a)
    (retractBasis_directed ha x)
  have : (x : Pomega) = (sSup (retractBasis a x) : Fixpoints (funOf a)) :=
    congrArg Subtype.val h
  exact this.trans hsu

end DomainTheory.DataTypesAsLattices
