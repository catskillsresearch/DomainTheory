/-ai
Every finite-image basis element of a fixed point of a retract is way below that fixed point. The retract hypothesis is not used.

Let a directed set of fixed points have supremum above the point. The basis witness is a finite set e n contained in the point, with the basis element equal to the retract applied to e n. The underlying supremum is the union of the underlying values, so e n is contained in that union. The finite-cover lemma for directed unions, using finiteness of e n, yields a member containing e n, and monotonicity of application together with the fixed-point equation for that member puts the basis element below it.
ai-/
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
