/-ai
The underlying set of a fixed point of a retract equals the union of the underlying sets of its finite-image basis elements.

The point equals the supremum of the basis, and the underlying set of that supremum equals the union of the basis values by Scott continuity of application and directedness of the basis.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.sSup_fixed_eq_sUnion
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_directed
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_sSup

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem retractBasis_sUnion {a : Pomega} (ha : IsRetract a)
    (x : Fixpoints (funOf a)) :
    (x : Pomega) = ⋃₀ (Subtype.val '' retractBasis a x) := by
  have h := retractBasis_sSup ha x
  have hsu := sSup_fixed_eq_sUnion (funOf_isScottContinuous a)
    (retractBasis_directed ha x)
  have : (x : Pomega) = (sSup (retractBasis a x) : Fixpoints (funOf a)) :=
    congrArg Subtype.val h
  exact this.trans hsu

end DomainTheory.DataTypesAsLattices
