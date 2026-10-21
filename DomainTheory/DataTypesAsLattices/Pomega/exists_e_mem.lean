/-ai
If k belongs to x, then some coded finite set is contained in x and contains k.

The singleton coded by 2^k is contained in x and contains k.
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
public import DomainTheory.DataTypesAsLattices.Pomega.e_pow2

@[expose] public section


namespace DomainTheory.DataTypesAsLattices













theorem exists_e_mem {x : Pomega} {k : ℕ} (hk : k ∈ x) :
    ∃ n, e n ⊆ x ∧ k ∈ e n :=
  ⟨2 ^ k, by simp [e_pow2, Set.singleton_subset_iff, hk], by simp [e_pow2]⟩

end DomainTheory.DataTypesAsLattices
