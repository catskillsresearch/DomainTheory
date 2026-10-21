/-ai
The found flag of the depth-n fold after N steps equals one if and only if some index below N has a non-empty D-side atom at the bit-source shifted by two to the depth.

The argument is by induction on N. The zero fold has found flag zero, so both sides fail. At a successor the fold is one step, which unfolds to a selection on the emptiness value, and that value is zero or one. If it is zero, the inner selection has found component one whether the previous flag is zero or one, using that the previous flag is at most one, and the new index is a witness. If it is one, the selection keeps the previous accumulator, the inductive equivalence applies, and a witness below the successor is a witness below N, since the new index has emptiness value one.
ai-/
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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.yFold_found_le_one

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


/-- **The "found" flag exactly tracks existence of a non-junk bit-source below `N`.** -/
theorem yFold_found_iff (n : ℕ) :
    ∀ N, (yFold P n N).unpair.1 = 1 ↔ ∃ i < N, atomUEmpty P (n + 1) (i + 2 ^ n) = 0 := by
  intro N
  induction N with
  | zero => simp [yFold_zero]
  | succ N ih =>
    rw [yFold_succ, yFoldStep_eq]
    rcases atomUEmpty_zero_or_one P (n + 1) (N + 2 ^ n) with h0 | h1
    · rw [h0, selectFn_zero]
      have hval1 : (selectFn (yFold P n N).unpair.1
          (Nat.pair 1 (unionUX (yFold P n N).unpair.2 (atomUCode P (n + 1) (N + 2 ^ n))))
          (Nat.pair 1 (atomUCode P (n + 1) (N + 2 ^ n)))).unpair.1 = 1 := by
        have hle := yFold_found_le_one P n N
        rcases Nat.eq_zero_or_pos (yFold P n N).unpair.1 with hf | hf
        · rw [show (yFold P n N).unpair.1 = 0 from hf, selectFn_zero, unpair_pair_fst]
        · rw [show (yFold P n N).unpair.1 = 1 from by omega, selectFn_one, unpair_pair_fst]
      rw [hval1]
      exact ⟨fun _ => ⟨N, Nat.lt_succ_self N, h0⟩, fun _ => rfl⟩
    · rw [h1, selectFn_one, ih]
      constructor
      · rintro ⟨i, hi, hie⟩; exact ⟨i, Nat.lt_succ_of_lt hi, hie⟩
      · rintro ⟨i, hi, hie⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
        · exact ⟨i, hi', hie⟩
        · exact absurd hie (by omega)

end DomainTheory.NeighbourhoodSystems
