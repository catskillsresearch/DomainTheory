/-ai
Unpairing the Cantor pair of n and m returns the ordered pair (n, m).

Pairing the components of that unpairing returns the original pair. Injectivity of pairing forces the two components to be n and m.
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
public import DomainTheory.DataTypesAsLattices.Pomega.pair_inj
public import DomainTheory.DataTypesAsLattices.Pomega.pair_unpair

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






















theorem unpair_pair (n m : ℕ) : unpair (pair n m) = (n, m) := by
  have h := pair_unpair (pair n m)
  exact Prod.ext (pair_inj h).1 (pair_inj h).2

end DomainTheory.DataTypesAsLattices
