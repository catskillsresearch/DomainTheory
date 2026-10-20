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
public import DomainTheory.DataTypesAsLattices.Pomega.e_or

@[expose] public section


namespace DomainTheory.DataTypesAsLattices













theorem e_or_of_subset {n m : ℕ} {x : Pomega} (hn : e n ⊆ x) (hm : e m ⊆ x) :
    e (n ||| m) ⊆ x := by
  rw [e_or]
  exact Set.union_subset hn hm

end DomainTheory.DataTypesAsLattices
