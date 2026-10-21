/-ai
Applying the Myhill set of the natural valuation and a function p to an element x equals the union, over every code j whose finite set is contained in x, of the natural value of p at the finite code of j. Both inclusions are the direct calculation of the Myhill–Shepherdson relation as an enumeration operator.

If m lies in the application, some j contained in x carries the pair membership of theorem 3.5, so m lies in the value of p at the finite code of j and hence in the union. Conversely, membership in the double union supplies such a j and such a value membership, and the converse direction of theorem 3.5 returns the pair membership.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
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
