/-ai
The generated atom of the coded Y family against the master, taken along the bits of a bit-source, is empty exactly when the emptiness flag at that depth reads 1.

Induct on the depth. At depth 0 the flag reads 0, because the generated atom of the index sets is the universe, and the generated atom against the master is nonempty because the master is. At a successor the flag is 0 or 1. If it reads 0, the closed form says the atom equals a universal neighbourhood, which is nonempty, so the flag cannot read 1. If it reads 1 and the previous flag reads 0, the previous closed form and the junction lemma make the successor atom empty. If the previous flag is not 0, then it is 1, the inductive hypothesis makes the previous atom empty, and meeting the next branch keeps it empty.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_eq_genAtomYseqCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_inter_succ_empty_of_junk

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


























































/-- **`Yc P`'s `genAtom`-emptiness matches `atomUEmpty` exactly** (the code-native analogue of
`atomU_invariant`'s emptiness-matching clause "(■)"): combines `atomUCode_eq_genAtomYseqCode`
(non-junk, giving a nonempty `UX`-image) with `atomUCode_inter_succ_empty_of_junk` (the genuine
transition to junk) by induction on `n`. -/
theorem genAtom_Yc_empty_iff (n k : ℕ) :
    genAtom (Yc P) U.master (deltaOf k) n = ∅ ↔ atomUEmpty P n k = 1 := by
  induction n with
  | zero =>
    have h0 : atomUEmpty P 0 k = 0 := by
      have hne : genAtom (idxSet (e P)) Set.univ (deltaOf k) 0 ≠ ∅ := by
        show (Set.univ : Set ℕ) ≠ ∅
        exact Set.univ_nonempty.ne_empty
      exact (atomUEmpty_eq_zero_iff_genAtom P 0 k).mpr hne
    constructor
    · intro h
      exact absurd h (Set.Nonempty.ne_empty U.master_mem.2.1)
    · intro h; omega
  | succ n ih =>
    have hle : atomUEmpty P (n + 1) k ≤ 1 := datomDec_le_one P _
    rcases (by omega : atomUEmpty P (n + 1) k = 0 ∨ atomUEmpty P (n + 1) k = 1) with h1 | h1
    · have heq' := atomUCode_eq_genAtomYseqCode P k (n + 1) h1
      constructor
      · intro hempty
        rw [← heq'] at hempty
        exact absurd hempty (U_mem_UX _).2.1.ne_empty
      · intro hcontra; omega
    · by_cases hn0 : atomUEmpty P n k = 0
      · have heq := atomUCode_eq_genAtomYseqCode P k n hn0
        have hempty : genAtom (Yc P) U.master (deltaOf k) (n + 1) = ∅ := by
          show genAtom (Yc P) U.master (deltaOf k) n ∩
            (if deltaOf k n then Yc P n else U.master \ Yc P n) = ∅
          rw [← heq]
          exact atomUCode_inter_succ_empty_of_junk P hn0 h1
        exact ⟨fun _ => h1, fun _ => hempty⟩
      · push Not at hn0
        have hle0 : atomUEmpty P n k ≤ 1 := datomDec_le_one P _
        have hn1 : atomUEmpty P n k = 1 := by omega
        have hprev : genAtom (Yc P) U.master (deltaOf k) n = ∅ := ih.mpr hn1
        have hempty : genAtom (Yc P) U.master (deltaOf k) (n + 1) = ∅ := by
          show genAtom (Yc P) U.master (deltaOf k) n ∩
            (if deltaOf k n then Yc P n else U.master \ Yc P n) = ∅
          rw [hprev, Set.empty_inter]
        exact ⟨fun _ => h1, fun _ => hempty⟩

end DomainTheory.NeighbourhoodSystems
