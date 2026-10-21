/-ai
Inclusion of the finite set coded by n in the finite set coded by m is decidable. It is equivalent to the bounded statement that every k at most n which lies in the first set lies in the second: membership in the set coded by n forces k ≤ n, and the converse implication drops that bound.
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
public import DomainTheory.DataTypesAsLattices.Pomega.mem_botElem
public import DomainTheory.DataTypesAsLattices.Pomega.mem_topElem
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Pomega.mem_e
public import DomainTheory.DataTypesAsLattices.Pomega.mem_e_le
public import DomainTheory.DataTypesAsLattices.Pomega.BasicInst11

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

instance (n m : ℕ) : Decidable (e n ⊆ e m) :=
  decidable_of_iff (∀ k ≤ n, k ∈ e n → k ∈ e m) ⟨
    fun h k hk => h k (mem_e_le hk) hk,
    fun h _k _ hk => h hk⟩

end DomainTheory.DataTypesAsLattices
