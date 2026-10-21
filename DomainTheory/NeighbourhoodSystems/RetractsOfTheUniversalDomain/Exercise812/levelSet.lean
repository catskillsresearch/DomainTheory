/-ai
The level set of a level k and a mask m is the set of natural numbers whose remainder modulo 2^k has its bit set in m. It is the union of the residue classes at that level selected by the bits of m.
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812.mem_affine

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

/-- The union of the residue classes `affine k ℓ` for `ℓ < 2^k` with `m.testBit ℓ = true`. Every
finite union of `affine`-sets sharing the *same* level `k` is of this form for a unique `m`
(`Finset.range (2^k)` residues partition `ℕ`, unlike arbitrary rational intervals), so a single
natural number `m` replaces the `List` bookkeeping `Definition87.lean` needs for `𝒰`. -/
def levelSet (k m : ℕ) : Set ℕ := {n : ℕ | m.testBit (n % 2 ^ k) = true}

end DomainTheory.NeighbourhoodSystems
