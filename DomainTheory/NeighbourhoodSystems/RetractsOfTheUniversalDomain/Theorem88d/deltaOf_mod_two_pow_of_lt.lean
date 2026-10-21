/-ai
Reducing a bit-source modulo two to the power n does not change bits strictly below n.

Rewrite both sides as test bits and apply the test-bit lemma for reduction modulo a power of two. The hypothesis that the position lies below n simplifies the result.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


/-- Reducing modulo `2ⁿ` never disturbs bits strictly below `n`. -/
theorem deltaOf_mod_two_pow_of_lt {k n i : ℕ} (hi : i < n) :
    deltaOf (k % 2 ^ n) i = deltaOf k i := by
  rw [deltaOf_eq_testBit, deltaOf_eq_testBit, Nat.testBit_mod_two_pow]
  simp [hi]

end DomainTheory.NeighbourhoodSystems
