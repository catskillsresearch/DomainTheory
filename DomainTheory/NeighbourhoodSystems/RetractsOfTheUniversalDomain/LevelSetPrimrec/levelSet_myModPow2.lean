module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myModPow2
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.myModPow2_eq

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `levelSet k (myModPow2 x (2^k)) = levelSet k x`: truncating a mask to its meaningful low
`2^k` bits never changes the `levelSet` it presents (`levelSet k _` only ever reads bit positions
`< 2^k`). Used to keep `myUpsample`'s output *bounded* (`myUpsample_lt`) even when no genuine
upsampling step occurs (`k = k'`), which the raw iteration alone would not guarantee. -/
theorem levelSet_myModPow2 (k x : ℕ) : levelSet k (myModPow2 x (2 ^ k)) = levelSet k x := by
  ext n
  simp only [mem_levelSet, myModPow2_eq, Nat.testBit_mod_two_pow]
  have : n % 2 ^ k < 2 ^ k := Nat.mod_lt n (Nat.two_pow_pos k)
  simp [this]

end DomainTheory.NeighbourhoodSystems
