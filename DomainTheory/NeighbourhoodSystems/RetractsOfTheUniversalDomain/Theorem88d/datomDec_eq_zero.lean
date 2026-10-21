/-ai
If the D-atom decoded from a pair of list codes is nonempty, the extracted decider reads 0 on that pair.

The decider is at most 1, and it does not read 1, because a reading of 1 would mean that the atom is empty.
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




/-- The complementary fact to `datomDec_spec`: whenever the `D`-side atom is *non*-empty,
`datomDec` reads out exactly `0` (not just "`≠ 1`") — needed so `selectFn`'s zero-branch actually
fires in the per-step unfoldings below. -/
theorem datomDec_eq_zero (posC negC : ℕ) (h : DAtom (P0 P) (decodeList posC) (decodeList negC) ≠ ∅) :
    datomDec P (Nat.pair posC negC) = 0 := by
  have hle := datomDec_le_one P (Nat.pair posC negC)
  have hne : datomDec P (Nat.pair posC negC) ≠ 1 := fun he => h ((datomDec_spec P posC negC).mp he)
  omega

end DomainTheory.NeighbourhoodSystems
