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

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

instance (n m : ℕ) : Decidable (e n ⊆ e m) :=
  decidable_of_iff (∀ k ≤ n, k ∈ e n → k ∈ e m) ⟨
    fun h k hk => h k (mem_e_le hk) hk,
    fun h _k _ hk => h hk⟩

end DomainTheory.DataTypesAsLattices
