module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem pair_unpair (k : ℕ) : pair (unpair k).1 (unpair k).2 = k :=
  (exists_pair k).choose_spec.choose_spec

end DomainTheory.DataTypesAsLattices
