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


/-- Unfolding `yFoldStep` at an explicit `(n, i, acc)` triple. -/
theorem yFoldStep_eq (n i acc : ℕ) :
    yFoldStep P (Nat.pair n (Nat.pair i acc)) =
      selectFn (atomUEmpty P (n + 1) (i + 2 ^ n)) acc
        (selectFn acc.unpair.1
          (Nat.pair 1 (unionUX acc.unpair.2 (atomUCode P (n + 1) (i + 2 ^ n))))
          (Nat.pair 1 (atomUCode P (n + 1) (i + 2 ^ n)))) := by
  unfold yFoldStep
  simp only [unpair_pair_fst, unpair_pair_snd]

end DomainTheory.NeighbourhoodSystems
