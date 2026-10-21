/-ai
A natural number lies in the residue class of ℓ modulo 2^k if and only if it is congruent to ℓ modulo 2^k.

The two sides are the defining membership condition of the residue class.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Nat.BitIndices
import all Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Combinatorics.Colex
import all Mathlib.Combinatorics.Colex
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.affine

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

@[simp] theorem mem_affine {k ℓ n : ℕ} : n ∈ affine k ℓ ↔ n % 2 ^ k = ℓ := Iff.rfl

end DomainTheory.NeighbourhoodSystems
