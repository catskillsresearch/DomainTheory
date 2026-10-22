module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_5_q

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- Both inclusions in the direct calculation of the Myhill–Shepherdson
relation as an enumeration operator. -/
theorem myhillQ_app (p : ℕ → ℕ) (x : Pomega) :
    funOf (myhillQ valNat p) x =
      ⋃ j, ⋃ (_ : e j ⊆ x), valNat (p (fin j)) := by
  ext m
  constructor
  · rintro ⟨j, hj, hpair⟩
    have hm : m ∈ valNat (p (fin j)) :=
      (theorem_3_5_q valNat p j m).mp hpair
    exact Set.mem_iUnion.mpr
      ⟨j, Set.mem_iUnion.mpr ⟨hj, hm⟩⟩
  · intro hm
    obtain ⟨j, hm⟩ := Set.mem_iUnion.mp hm
    obtain ⟨hj, hm⟩ := Set.mem_iUnion.mp hm
    exact ⟨j, hj, (theorem_3_5_q valNat p j m).mpr hm⟩

end DomainTheory.DataTypesAsLattices
