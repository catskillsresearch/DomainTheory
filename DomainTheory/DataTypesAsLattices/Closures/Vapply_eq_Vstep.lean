
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Vapply_closed

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Vapply_eq_Vstep (a x : Pomega) :
    Vapply a x = Vstep a x (Vapply a x) := by
  apply subset_antisymm
  · intro k hk
    have hset : x ∪ funOf a (Vapply a x) ∈
        {y | x ⊆ y ∧ funOf a y ⊆ y} :=
      ⟨Set.subset_union_left, fun m hm =>
        Set.subset_union_right
          (isScottContinuous_monotone (funOf_isScottContinuous a)
            (Vapply_closed a x) hm)⟩
    exact hk (x ∪ funOf a (Vapply a x)) hset
  · exact Vapply_closed a x

end DomainTheory.DataTypesAsLattices
