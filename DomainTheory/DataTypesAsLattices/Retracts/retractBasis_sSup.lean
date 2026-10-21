/-ai
A fixed point of a retract equals the supremum of its finite-image basis.

Compare underlying sets. The supremum in the fixed-point lattice has underlying set equal to the union of the basis values, by Scott continuity of application and directedness of the basis. Typing of the fixed point and the interpolation law rewrite the point as the union of those indices that lie in the retract applied to some finite set contained in the point. Such an index belongs to the corresponding basis value, and an index of a basis value lies in that interpolated union.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.retract_interpolation
public import DomainTheory.DataTypesAsLattices.Retracts.sSup_fixed_eq_sUnion
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_directed

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem retractBasis_sSup {a : Pomega} (ha : IsRetract a)
    (x : Fixpoints (funOf a)) :
    x = sSup (retractBasis a x) := by
  apply Subtype.ext
  rw [sSup_fixed_eq_sUnion (funOf_isScottContinuous a)
    (retractBasis_directed ha x)]
  have hx : typed (x : Pomega) a := x.property.symm
  rw [retract_interpolation ha hx]
  ext k
  constructor
  · intro hk
    obtain ⟨n, hnx, hkn⟩ := Set.mem_iUnion.mp hk
    let y : Fixpoints (funOf a) :=
      ⟨funOf a (e n), retract_app ha (e n)⟩
    exact Set.mem_sUnion.mpr
      ⟨y, ⟨y, ⟨n, hnx, rfl⟩, rfl⟩, hkn⟩
  · intro hk
    obtain ⟨_, ⟨y, ⟨n, hnx, hyn⟩, rfl⟩, hky⟩ :=
      Set.mem_sUnion.mp hk
    exact Set.mem_iUnion.mpr ⟨n, hnx, hyn ▸ hky⟩

end DomainTheory.DataTypesAsLattices
