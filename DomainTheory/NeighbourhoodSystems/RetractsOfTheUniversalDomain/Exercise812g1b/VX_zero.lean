module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g1b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g1b.levelSet_zero_zero

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `hY0`: index `0` presents `V`'s master neighbourhood. `Nat.unpair 0 = (0, 0)` and
`levelSet 0 0 = ∅`, so `canonIdx 0` falls back to `VmasterIdx = Nat.pair 0 1`
(`canonIdx_eq_master_of_empty`), whose `VX`-image is `V.master` (`VX_VmasterIdx`). -/
theorem VX_zero : VX 0 = V.master := by
  have hc0 : canonIdx 0 = VmasterIdx :=
    canonIdx_eq_master_of_empty (by rw [Nat.unpair_zero]; exact levelSet_zero_zero)
  rw [← VX_canonIdx 0, hc0]
  exact VX_VmasterIdx

end DomainTheory.NeighbourhoodSystems
