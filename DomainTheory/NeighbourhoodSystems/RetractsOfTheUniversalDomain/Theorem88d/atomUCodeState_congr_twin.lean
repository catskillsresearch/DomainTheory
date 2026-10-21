/-ai
The positive twin of a bit-source at depth n, namely its residue modulo two to the power n plus that power, has the same positive code, the same negative code, and the same U-code as the original bit-source.

The twin agrees with the original on every bit below n, because adding the power preserves those bits and reduction modulo the power preserves them as well. The state congruence therefore applies.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.deltaOf_mod_two_pow_of_lt

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

























































/-- **The canonical "positive twin" at depth `n`** shares `k`'s own `(pos, neg, code)` triple, since
it agrees with `k` on every bit below `n` (`atomUCodeState_congr` applied to
`k % 2ⁿ`/`deltaOf_mod_two_pow_of_lt`/`deltaOf_add_two_pow_of_lt`). -/
theorem atomUCodeState_congr_twin (n k : ℕ) :
    atomUPos P n (k % 2 ^ n + 2 ^ n) = atomUPos P n k ∧
      atomUNeg P n (k % 2 ^ n + 2 ^ n) = atomUNeg P n k ∧
      atomUCode P n (k % 2 ^ n + 2 ^ n) = atomUCode P n k := by
  have hagree : ∀ i < n, deltaOf (k % 2 ^ n + 2 ^ n) i = deltaOf k i := by
    intro i hi
    rw [deltaOf_add_two_pow_of_lt _ hi, deltaOf_mod_two_pow_of_lt hi]
  exact atomUCodeState_congr P hagree

end DomainTheory.NeighbourhoodSystems
