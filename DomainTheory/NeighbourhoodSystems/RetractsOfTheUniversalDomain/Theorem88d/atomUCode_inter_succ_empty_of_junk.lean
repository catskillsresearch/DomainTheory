module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.eIdx_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.he0
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.hcover
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88b.genAtom_empty_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.datomDec_eq_zero
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.deltaOf_mod_two_pow_of_lt
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_succ_true
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCode_disjoint_YseqCode_of_posTwin_empty
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.atomUCodeState_congr_twin
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88d.DAtom_union

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


























































/-- **The junction lemma**: once a bit-source's atom is still non-empty at depth `n` but becomes
junk at depth `n + 1`, `genAtom`'s corresponding step (against `Yc P`/`U.master`) is already
empty. Two cases on `deltaOf k n`: `true` reduces directly to
`atomUCode_disjoint_YseqCode_of_posTwin_empty` (`k` already *is* its own positive twin); `false`
needs the extra fact that the depth-`n` atom's own code is *unchanged* by its positive twin (since
the "negative refinement" being `D`-side empty forces the whole atom into the positive side,
`DAtom_union`), so `atomUCode_succ_true` at the twin identifies `atomUCode P n k` with the
intersection against `YseqCode`'s union outright, i.e. `UX (atomUCode P n k) ⊆ Yc P n`. -/
theorem atomUCode_inter_succ_empty_of_junk {n k : ℕ} (hn0 : atomUEmpty P n k = 0)
    (hjunk : atomUEmpty P (n + 1) k = 1) :
    UX (atomUCode P n k) ∩ (if deltaOf k n then Yc P n else U.master \ Yc P n) = ∅ := by
  -- `Bool.eq_false_or_eq_true` enumerates `true` before `false`.
  rcases Bool.eq_false_or_eq_true (deltaOf k n) with hδ | hδ
  · -- `k` itself already has bit `n` set: `k` is (mod `2 ^ (n + 1)`) its own positive twin.
    have hjlt0 : k % 2 ^ n < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
    have hagree : ∀ l < n + 1, deltaOf (k % 2 ^ n + 2 ^ n) l = deltaOf k l := by
      intro l hl
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl' | rfl
      · rw [deltaOf_add_two_pow_of_lt _ hl', deltaOf_mod_two_pow_of_lt hl']
      · rw [deltaOf_two_pow_add_self hjlt0, hδ]
    obtain ⟨hp, hnge, -⟩ := atomUCodeState_congr P hagree
    have htwinJunk : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) = 1 := by
      unfold atomUEmpty
      rw [hp, hnge]
      exact hjunk
    rw [ite_eq_left hδ]
    exact atomUCode_disjoint_YseqCode_of_posTwin_empty P hn0 htwinJunk
  · -- `k` has bit `n` unset: the "negative refinement" alone is empty, so `k`'s own atom already
    -- coincides with its positive twin's atom (`DAtom_union`), which forces junk at `n + 1`.
    have hbit0 : (k / 2 ^ n) % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (k / 2 ^ n) with hh | hh
      · exact hh
      · exact absurd ((deltaOf_eq_true_iff k n).mpr hh) (by simp [hδ])
    have hempJ : datomDec P (Nat.pair (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)) = 1 := by
      have h := hjunk
      rw [atomUEmpty_succ, hbit0, selectFn_zero] at h
      exact h
    have hJempty : DAtom (P0 P) (decodeList (atomUPos P n k))
        (n :: decodeList (atomUNeg P n k)) = ∅ := by
      have h := (datomDec_spec P (atomUPos P n k) (Nat.pair n (atomUNeg P n k) + 1)).mp hempJ
      rwa [decodeList_succ, unpair_pair_fst, unpair_pair_snd] at h
    have hDunion := DAtom_union P n (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k))
    have hIeqAll : DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) =
        DAtom (P0 P) (n :: decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) := by
      rw [hDunion, hJempty, Set.union_empty]
    have hIeqAll' : DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) =
        DAtom (P0 P) (decodeList (Nat.pair n (atomUPos P n k) + 1)) (decodeList (atomUNeg P n k)) := by
      rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd]; exact hIeqAll
    have hne0 : DAtom (P0 P) (decodeList (atomUPos P n k)) (decodeList (atomUNeg P n k)) ≠ ∅ := by
      intro hcon
      have := (atomUEmpty_eq_one_iff P n k).mpr hcon
      omega
    have hemptyI0 : datomDec P (Nat.pair (Nat.pair n (atomUPos P n k) + 1) (atomUNeg P n k)) = 0 := by
      apply datomDec_eq_zero
      rw [← hIeqAll']
      exact hne0
    have hjlt : k % 2 ^ n < 2 ^ n := Nat.mod_lt k (Nat.two_pow_pos n)
    obtain ⟨htwinPos, htwinNeg, htwinCode⟩ := atomUCodeState_congr_twin P n k
    have htwinBit1 : (k % 2 ^ n + 2 ^ n) / 2 ^ n % 2 = 1 := by
      have hh := deltaOf_two_pow_add_self hjlt
      rw [deltaOf_eq_true_iff] at hh
      exact hh
    have htwinNonjunk : atomUEmpty P (n + 1) (k % 2 ^ n + 2 ^ n) = 0 := by
      rw [atomUEmpty_succ, htwinBit1, selectFn_one, htwinPos, htwinNeg]
      exact hemptyI0
    have hδtwin : deltaOf (k % 2 ^ n + 2 ^ n) n = true := deltaOf_two_pow_add_self hjlt
    have hkey := atomUCode_succ_true P htwinNonjunk hδtwin
    have htwinCodeVal : atomUCode P (n + 1) (k % 2 ^ n + 2 ^ n) = atomUCode P n k := by
      rw [atomUCode_succ, htwinBit1, selectFn_one, htwinPos, htwinNeg, hemptyI0, selectFn_zero,
        htwinCode, hempJ, selectFn_one]
    rw [htwinCodeVal, htwinCode] at hkey
    have hsub : UX (atomUCode P n k) ⊆ Yc P n := by
      intro z hz
      have hz' : z ∈ UX (atomUCode P n k) ∩ UX (YseqCode P n) := by rw [← hkey]; exact hz
      exact hz'.2
    rw [ite_eq_right (by simp [hδ])]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz1, -, hz2⟩
    exact hz2 (hsub hz1)

end DomainTheory.NeighbourhoodSystems
