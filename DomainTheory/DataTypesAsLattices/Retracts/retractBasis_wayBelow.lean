module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.directed_finite_cover
public import DomainTheory.DataTypesAsLattices.Retracts.sSup_fixed_eq_sUnion

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem retractBasis_wayBelow {a : Pomega} (_ha : Retract a)
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
  have := isScottContinuous_monotone (funOf_isScottContinuous a) hnz
  rwa [z.property] at this

end DomainTheory.DataTypesAsLattices
