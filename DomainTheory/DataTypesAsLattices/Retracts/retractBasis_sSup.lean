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
