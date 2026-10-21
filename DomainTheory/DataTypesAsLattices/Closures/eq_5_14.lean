/-ai
Scott 1976, (5.14), identified with (5.15). The least fixed point of the step that adjoins x and closes under a equals the intersection of all sets that contain x and are closed under a.

The least-fixed-point theorem fixes the iterative value. One inclusion is the minimality clause of that theorem at the intersection, using the step equation for the intersection. For the other inclusion, the fixed-point equation puts x into the iterative value by the left summand of the step and puts the application of a into it by the right summand, so the iterative value is one of the sets being intersected.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Vstep_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.Vapply_eq_Vstep

@[expose] public section


namespace DomainTheory.DataTypesAsLattices




















/-- **Scott 1976, (5.14) = (5.15).** -/
theorem eq_5_14 (a x : Pomega) : VapplyY a x = Vapply a x := by
  have hfix : Vstep a x (VapplyY a x) = VapplyY a x :=
    (theorem_1_4 (Vstep_isScottContinuous a x)).1
  apply subset_antisymm
  · exact (theorem_1_4 (Vstep_isScottContinuous a x)).2 (Vapply a x)
      (Vapply_eq_Vstep a x).symm
  · intro k hk
    have hx : x ⊆ VapplyY a x := by
      intro m hm
      have : m ∈ Vstep a x (VapplyY a x) := Or.inl hm
      rwa [hfix] at this
    have ha : funOf a (VapplyY a x) ⊆ VapplyY a x := by
      intro m hm
      have : m ∈ Vstep a x (VapplyY a x) := Or.inr hm
      rwa [hfix] at this
    exact hk (VapplyY a x) ⟨hx, ha⟩

end DomainTheory.DataTypesAsLattices
