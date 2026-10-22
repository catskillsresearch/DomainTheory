/-ai
The finite-image basis of a fixed point of a retract is a directed set.

The retract applied to the finite set e 0 is a fixed point by the retract application law, and e 0 is contained in the point, so that fixed point lies in the basis. Given basis elements from e n and e m, the retract applied to the finite set of the bitwise join is a basis element above both: that finite set contains each of e n and e m, and application of the retract is monotone.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem retractBasis_directed {a : Pomega} (ha : Retract a)
    (x : Fixpoints (funOf a)) :
    IsDirectedSet (retractBasis a x) := by
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
      exact isScottContinuous_monotone (funOf_isScottContinuous a)
        Set.subset_union_left
    · change (z : Pomega) ⊆ (w : Pomega)
      rw [hzm]
      change funOf a (e m) ⊆ funOf a (e (n ||| m))
      rw [e_or]
      exact isScottContinuous_monotone (funOf_isScottContinuous a)
        Set.subset_union_right

end DomainTheory.DataTypesAsLattices
