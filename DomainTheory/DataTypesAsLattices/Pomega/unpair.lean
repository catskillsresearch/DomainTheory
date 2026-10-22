module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.mem_botElem
public import DomainTheory.DataTypesAsLattices.Pomega.mem_topElem
public import DomainTheory.DataTypesAsLattices.Pomega.mem_e
public import DomainTheory.DataTypesAsLattices.Pomega.BasicInst11
public import DomainTheory.DataTypesAsLattices.Pomega.BasicInst12
public import DomainTheory.DataTypesAsLattices.Pomega.exists_pair

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Inverse of Cantor pairing. -/
noncomputable def unpair (k : ℕ) : ℕ × ℕ :=
  ((exists_pair k).choose, (exists_pair k).choose_spec.choose)

end DomainTheory.DataTypesAsLattices
