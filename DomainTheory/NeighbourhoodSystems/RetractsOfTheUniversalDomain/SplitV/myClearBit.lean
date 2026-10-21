/-ai
myClearBit m ell subtracts two to the power ell from m. Whenever bit ell of m is set, this equals m with that bit cleared by exclusive or.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.MinLevel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive

/-- **The "clear one bit" primitive.** `myClearBit m ℓ := m - 2 ^ ℓ` — primitive recursive for
free (plain subtraction and a power of two), and, whenever bit `ℓ` of `m` is genuinely set,
literally equal to `m ^^^ 2 ^ ℓ` (`myClearBit_eq_xor`). -/
def myClearBit (m ℓ : ℕ) : ℕ := m - 2 ^ ℓ

end DomainTheory.NeighbourhoodSystems
