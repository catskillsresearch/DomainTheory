module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.yFold_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.yFold_succ
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUEmpty_zero_or_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.yFoldStep_eq

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


theorem yFold_found_le_one (n : ℕ) : ∀ N, (yFold P n N).unpair.1 ≤ 1 := by
  intro N
  induction N with
  | zero => simp [yFold_zero]
  | succ N ih =>
    rw [yFold_succ, yFoldStep_eq]
    rcases atomUEmpty_zero_or_one P (n + 1) (N + 2 ^ n) with h0 | h1
    · rw [h0, selectFn_zero]
      rcases Nat.eq_zero_or_pos (yFold P n N).unpair.1 with hf0 | hfpos
      · rw [show (yFold P n N).unpair.1 = 0 from hf0, selectFn_zero, unpair_pair_fst]
      · rw [show (yFold P n N).unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]
    · rw [h1, selectFn_one]; exact ih

end DomainTheory.NeighbourhoodSystems
