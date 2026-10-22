/-ai
If the finite sets coded by n and by m are both contained in x, then the finite set coded by their bitwise disjunction is contained in x.

Rewrite by the disjunction law for codes and combine the two inclusions.
ai-/
module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Basic
public import DomainTheory.DataTypesAsLattices.Pomega.e_or

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem e_or_of_subset {n m : ℕ} {x : Pomega} (hn : e n ⊆ x) (hm : e m ⊆ x) :
    e (n ||| m) ⊆ x := by
  rw [e_or]
  exact Set.union_subset hn hm

end DomainTheory.DataTypesAsLattices
