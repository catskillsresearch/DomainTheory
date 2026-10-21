/-ai
If a bit-source is non-junk at depth n+1 and its bit at n is false, the universal neighbourhood of the new code is the old neighbourhood with the coded Y neighbourhood removed.

The positive twin agrees with the bit-source at depth n. The bit is 0, so the negative check reads 0, and the new code selects between the old code and its right split according to the positive check, which is the twin's emptiness flag. If that flag reads 0, the twin's code is the left split of the old code. The true-branch formula identifies the left split with the part inside the coded Y sequence, and the union and disjointness of the two splits give the right split as the complement of the left split. If the flag reads 1, the twin is junk, so the old neighbourhood is already disjoint from the coded Y sequence, the code stays the old one, and removing that sequence changes nothing.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCodeState_congr_twin

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)


variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


/-- **The closed form, "false"-branch** (mirroring `Theorem88.lean`'s `atomU_succ_eq`'s `else`
case): for non-junk `k` with bit `n` forced `false`, the depth-`(n+1)` atom is the depth-`n` atom
*minus* `YseqCode`. Two sub-cases on whether `k`'s own "positive twin" (bits agreeing below `n`,
bit `n` forced `true`) is itself junk: if junk, the whole depth-`n` atom is already disjoint from
`YseqCode`'s union (`atomUCode_disjoint_YseqCode_of_posTwin_empty`), so subtracting it changes
nothing; if non-junk, the twin's own code is literally `splitULeft (atomUCode P n k)` (unfolding
both `atomUCode_succ`'s at the shared ancestor), so `atomUCode_succ_true` applied to the twin
identifies `splitULeft`'s image with `YseqCode`'s contribution, and `splitU_union`/`splitU_disjoint`
finish the algebra `UX(splitURight c) = UX c \ UX(splitULeft c)`. -/
theorem atomUCode_succ_false {k n : ℕ} (hne : atomUEmpty P (n + 1) k = 0)
    (hδ : deltaOf k n = false) :
    UX (atomUCode P (n + 1) k) = UX (atomUCode P n k) \ UX (YseqCode P n) := by
  have hjlt : k % 2 ^ n < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
  obtain ⟨htwinPos, htwinNeg, htwinCode⟩ := atomUCodeState_congr_twin P n k
  have hbit0 : (k / 2 ^ n) % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hh | hh
    · exact hh
    · exact absurd ((deltaOf_eq_true_iff k n).mpr hh) (by simp [hδ])
  have hempJ : datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)) = 0 := by
    have h := hne
    rw [atomUEmpty_succ, hbit0, selectFn_zero] at h
    exact h
  have hncode : atomUCode P (n + 1) k = selectFn
      (datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)))
      (atomUCode P n k) (splitURight (atomUCode P n k)) := by
    rw [atomUCode_succ, hbit0, selectFn_zero, hempJ, selectFn_zero]
  have htwinBit1 : (k % 2 ^ n + 2 ^ n) / 2 ^ n % 2 = 1 := by
    have hh := deltaOf_two_pow_add_self hjlt
    rw [deltaOf_eq_true_iff] at hh
    exact hh
  have htwinEmpty : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) =
      datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) := by
    rw [atomUEmpty_succ, htwinBit1, selectFn_one, htwinPos, htwinNeg]
  have hIle := datomDec_le_one P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k))
  rcases (by omega :
      datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 0 ∨
      datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 1) with hI | hI
  · -- Genuine split at the shared ancestor: the twin's own code is `splitULeft (atomUCode P n k)`.
    have htwinCodeVal : atomUCode P (n + 1) (k % 2 ^ n + 2 ^ n) = splitULeft (atomUCode P n k) := by
      rw [atomUCode_succ, htwinBit1, selectFn_one, htwinPos, htwinNeg, htwinCode, hI, selectFn_zero,
        hempJ, selectFn_zero]
    have htwinNonjunk : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) = 0 := by rw [htwinEmpty, hI]
    have hδtwin : deltaOf (k % 2 ^ n + 2 ^ n) n = true := deltaOf_two_pow_add_self hjlt
    have hkey := atomUCode_succ_true P htwinNonjunk hδtwin
    rw [htwinCodeVal, htwinCode] at hkey
    have hunion := splitU_union (atomUCode P n k)
    have hdisj := splitU_disjoint (atomUCode P n k)
    have hUXeq : UX (splitURight (atomUCode P n k)) =
        UX (atomUCode P n k) \ UX (splitULeft (atomUCode P n k)) := by
      apply Set.Subset.antisymm
      · intro z hz
        refine ⟨?_, fun hzL => ?_⟩
        · rw [← hunion]; exact Set.mem_union_right _ hz
        · have hz' : z ∈ UX (splitULeft (atomUCode P n k)) ∩ UX (splitURight (atomUCode P n k)) :=
            ⟨hzL, hz⟩
          rw [hdisj] at hz'
          exact hz'
      · rintro z ⟨hzC, hznL⟩
        rw [← hunion] at hzC
        exact hzC.resolve_left hznL
    rw [hncode, hI, selectFn_zero, hUXeq, hkey]
    apply Set.Subset.antisymm
    · rintro z ⟨hzC, hznCY⟩
      exact ⟨hzC, fun hzY => hznCY ⟨hzC, hzY⟩⟩
    · rintro z ⟨hzC, hznY⟩
      exact ⟨hzC, fun hzY => hznY hzY.2⟩
  · -- Junk twin: the whole depth-`n` atom is already disjoint from `YseqCode`'s union.
    have htwinNonjunk : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) = 1 := by rw [htwinEmpty, hI]
    have hk : atomUEmpty P n k = 0 := atomUEmpty_zero_of_succ P hne
    have hcdisj : UX (atomUCode P n k) ∩ UX (YseqCode P n) = ∅ :=
      atomUCode_disjoint_YseqCode_of_posTwin_empty P hk htwinNonjunk
    have hEq : UX (atomUCode P n k) = UX (atomUCode P n k) \ UX (YseqCode P n) := by
      apply Set.Subset.antisymm
      · intro z hz
        refine ⟨hz, fun hzY => ?_⟩
        have hz' : z ∈ UX (atomUCode P n k) ∩ UX (YseqCode P n) := ⟨hz, hzY⟩
        rw [hcdisj] at hz'
        exact hz'
      · exact Set.sdiff_subset
    rw [hncode, hI, selectFn_one]
    exact hEq

end DomainTheory.NeighbourhoodSystems
