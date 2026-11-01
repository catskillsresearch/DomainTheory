module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace e

/-- Bit-mask code of a list of naturals: bitwise OR of $2^k$ over entries. -/
def codeList : List ℕ → ℕ
  | [] => 0
  | k :: ks => 2 ^ k ||| codeList ks

theorem codeList_eq (ks : List ℕ) : e (codeList ks) = {k | k ∈ ks} := by
  induction ks with
  | nil => simp [codeList, zero]
  | cons k ks ih =>
    ext i
    simp [codeList, or, pow2, ih]

noncomputable def codeFinset (s : Finset ℕ) : ℕ := codeList s.val.toList

theorem codeFinset_eq (s : Finset ℕ) : e (codeFinset s) = (s : Set ℕ) := by
  ext k
  simp [codeFinset, codeList_eq]

theorem exists_code (s : Finset ℕ) : ∃ n, e n = (s : Set ℕ) :=
  ⟨codeFinset s, codeFinset_eq s⟩

theorem exists_code_of_finite {s : Pomega} (hs : Set.Finite s) :
    ∃ n, e n = s := by
  obtain ⟨t, ht⟩ := hs.exists_finset_coe
  exact ⟨codeFinset t, ht ▸ codeFinset_eq t⟩

end e

end DomainTheory.DataTypesAsLattices
