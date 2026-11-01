module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def codeList : List ℕ → ℕ
  | [] => 0
  | k :: ks => 2 ^ k ||| codeList ks

noncomputable def codeFinset (s : Finset ℕ) : ℕ := codeList s.val.toList

theorem e_codeList (ks : List ℕ) : e (codeList ks) = {k | k ∈ ks} := by
  induction ks with
  | nil => simp [codeList, e.zero]
  | cons k ks ih =>
    ext i
    simp [codeList, e.or, e.pow2, ih]

theorem e_codeFinset (s : Finset ℕ) : e (codeFinset s) = (s : Set ℕ) := by
  ext k
  simp [codeFinset, e_codeList]

theorem exists_code (s : Finset ℕ) : ∃ n, e n = (s : Set ℕ) :=
  ⟨codeFinset s, e_codeFinset s⟩

theorem exists_code_of_finite {s : Pomega} (hs : Set.Finite s) :
    ∃ n, e n = s := by
  obtain ⟨t, ht⟩ := hs.exists_finset_coe
  exact ⟨codeFinset t, ht ▸ e_codeFinset t⟩

end DomainTheory.DataTypesAsLattices
