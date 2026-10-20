module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_false

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


























































/-- **The closed-form correspondence** (mirrors `Theorem88.lean`'s `atomU_eq_genAtom`): whenever
`k`'s bit-source is still `D`-side non-empty at depth `n`, the `U`-code `atomUCode P n k` is
*exactly* the generic atom built from `Yc P`/`U.master` — proved by induction, using
`atomUCode_succ_true`/`atomUCode_succ_false` to match `genAtom`'s own recursive step verbatim. -/
theorem atomUCode_eq_genAtomYseqCode (k : ℕ) :
    ∀ n, atomUEmpty P n k = 0 → UX (atomUCode P n k) = genAtom (Yc P) U.master (deltaOf k) n := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [atomUCode_zero, UX_UmasterIdx]
    rfl
  | succ n ih =>
    intro hne
    have ihn := ih (atomUEmpty_zero_of_succ P hne)
    -- `Bool.eq_false_or_eq_true` enumerates `true` before `false`.
    rcases Bool.eq_false_or_eq_true (deltaOf k n) with hδ | hδ
    · have hstep : genAtom (Yc P) U.master (deltaOf k) (n + 1) =
          genAtom (Yc P) U.master (deltaOf k) n ∩ Yc P n := by
        show genAtom (Yc P) U.master (deltaOf k) n ∩
          (if deltaOf k n then Yc P n else U.master \ Yc P n) = _
        simp [hδ]
      rw [hstep, ← ihn, atomUCode_succ_true P hne hδ]
      rfl
    · have hstep : genAtom (Yc P) U.master (deltaOf k) (n + 1) =
          genAtom (Yc P) U.master (deltaOf k) n ∩ (U.master \ Yc P n) := by
        show genAtom (Yc P) U.master (deltaOf k) n ∩
          (if deltaOf k n then Yc P n else U.master \ Yc P n) = _
        simp [hδ]
      rw [hstep, ← ihn, atomUCode_succ_false P hne hδ]
      have hsub : UX (atomUCode P n k) ⊆ U.master := by
        rw [ihn]; exact genAtom_subset (Yc P) U.master (deltaOf k) n
      apply Set.Subset.antisymm
      · intro z hz; exact ⟨hz.1, hsub hz.1, hz.2⟩
      · rintro z ⟨hz1, -, hz2⟩; exact ⟨hz1, hz2⟩

end DomainTheory.NeighbourhoodSystems
