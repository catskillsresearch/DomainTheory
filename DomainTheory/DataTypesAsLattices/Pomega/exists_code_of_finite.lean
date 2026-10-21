/-ai
Every finite subset of the natural numbers is the finite set coded by some natural number.

Choose a finset with the same underlying set and take its code. The decoding law, transported along the equality of the two sets, gives the result.
ai-/
module

public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
import all Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
import all Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
import all Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Basic
public import DomainTheory.DataTypesAsLattices.Pomega.e_codeFinset

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem exists_code_of_finite {s : Pomega} (hs : s.Finite) :
    ∃ n, e n = s := by
  obtain ⟨t, ht⟩ := hs.exists_finset_coe
  exact ⟨codeFinset t, ht ▸ e_codeFinset t⟩

end DomainTheory.DataTypesAsLattices
