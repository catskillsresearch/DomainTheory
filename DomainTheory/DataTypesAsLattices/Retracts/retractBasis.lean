module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.Retract
public import DomainTheory.DataTypesAsLattices.Retracts.retract_app
public import DomainTheory.DataTypesAsLattices.Retracts.retract_interpolation
public import DomainTheory.DataTypesAsLattices.Retracts.sSup_fixed_eq_sUnion
public import DomainTheory.DataTypesAsLattices.Retracts.directed_finite_cover
public import DomainTheory.DataTypesAsLattices.FixedLattices.DirectedSet
public import DomainTheory.DataTypesAsLattices.Retracts.DirectedSubset
public import DomainTheory.DataTypesAsLattices.Graph.funOf_isScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- The canonical finite-image basis of the fixed-point lattice of a retract. -/
def retractBasis (a : Pomega) (x : Fixpoints (funOf a)) :
    Set (Fixpoints (funOf a)) :=
  {y | ∃ n, e n ⊆ x ∧ (y : Pomega) = funOf a (e n)}

namespace retractBasis

theorem directed {a : Pomega} (ha : Retract a)
    (x : Fixpoints (funOf a)) :
    DirectedSet (retractBasis a x) := by
  constructor
  constructor
  · let y : Fixpoints (funOf a) :=
      ⟨funOf a (e 0), retract_app ha (e 0)⟩
    exact ⟨y, 0, by simp [e_zero], rfl⟩
  · intro y hy z hz
    obtain ⟨n, hnx, hyn⟩ := hy
    obtain ⟨m, hmx, hzm⟩ := hz
    let w : Fixpoints (funOf a) :=
      ⟨funOf a (e (n ||| m)), retract_app ha (e (n ||| m))⟩
    refine ⟨w, ⟨n ||| m, e_or_of_subset hnx hmx, rfl⟩, ?_, ?_⟩
    · change (y : Pomega) ⊆ (w : Pomega)
      rw [hyn]
      change funOf a (e n) ⊆ funOf a (e (n ||| m))
      rw [e_or]
      exact IsScottContinuous.monotone (funOf_isScottContinuous a)
        Set.subset_union_left
    · change (z : Pomega) ⊆ (w : Pomega)
      rw [hzm]
      change funOf a (e m) ⊆ funOf a (e (n ||| m))
      rw [e_or]
      exact IsScottContinuous.monotone (funOf_isScottContinuous a)
        Set.subset_union_right

theorem directedSubset {a : Pomega} (ha : Retract a)
    (x : Fixpoints (funOf a)) :
    DirectedSubset (retractBasis a x) := by
  have h := directed ha x
  refine ⟨⟨h.out.1, ?_⟩⟩
  intro y hy z hz
  obtain ⟨w, hw, hyw, hzw⟩ := h.out.2 hy hz
  exact ⟨w, hw, hyw, hzw⟩

theorem eq_sSup {a : Pomega} (ha : Retract a)
    (x : Fixpoints (funOf a)) :
    x = sSup (retractBasis a x) := by
  apply Subtype.ext
  rw [sSup_fixed_eq_sUnion (funOf_isScottContinuous a)
    (directed ha x)]
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

theorem eq_sUnion {a : Pomega} (ha : Retract a)
    (x : Fixpoints (funOf a)) :
    (x : Pomega) = ⋃₀ (Subtype.val '' retractBasis a x) := by
  have h := eq_sSup ha x
  have hsu := sSup_fixed_eq_sUnion (funOf_isScottContinuous a)
    (directed ha x)
  have : (x : Pomega) = (sSup (retractBasis a x) : Fixpoints (funOf a)) :=
    congrArg Subtype.val h
  exact this.trans hsu

theorem wayBelow {a : Pomega} (_ha : Retract a)
    {x y : Fixpoints (funOf a)} (hy : y ∈ retractBasis a x) :
    WayBelow y x := by
  intro A hA hxA
  obtain ⟨n, hnx, hyn⟩ := hy
  have hsup :
      ((sSup A : Fixpoints (funOf a)) : Pomega) =
        ⋃₀ (Fixpoints.vals A) :=
    sSup_fixed_eq_sUnion (funOf_isScottContinuous a) hA
  have hfinite :
      e n ⊆ ⋃₀ (Fixpoints.vals A) := by
    rw [← hsup]
    exact hnx.trans hxA
  obtain ⟨z, hzA, hnz⟩ :=
    directed_finite_cover hA (e_finite n) hfinite
  refine ⟨z, hzA, ?_⟩
  change (y : Pomega) ⊆ z
  rw [hyn]
  have := IsScottContinuous.monotone (funOf_isScottContinuous a) hnz
  rwa [z.property] at this

end retractBasis

end DomainTheory.DataTypesAsLattices
