/-ai
The finite set coded by the bit-mask of a list is the set of entries of the list.

Proceed by induction on the list. The empty list codes the empty set. For a cons cell, extensionality together with the laws for bitwise disjunction and for a power of two, and the inductive hypothesis, identifies the coded set with membership in the list.
ai-/
module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Basic
public import DomainTheory.DataTypesAsLattices.Pomega.e_zero
public import DomainTheory.DataTypesAsLattices.Pomega.e_pow2
public import DomainTheory.DataTypesAsLattices.Pomega.e_or

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem e_codeList (ks : List ℕ) : e (codeList ks) = {k | k ∈ ks} := by
  induction ks with
  | nil => simp [codeList, e_zero]
  | cons k ks ih =>
    ext i
    simp [codeList, e_or, e_pow2, ih]

end DomainTheory.DataTypesAsLattices
