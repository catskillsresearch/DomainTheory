/-ai
Reading a word from the state that has matched a prefix of a given length reaches the state of that length plus the length of the word when the word is a prefix of the remaining suffix, and reaches the sink otherwise.

The proof is by induction on the word. The empty word is a prefix and leaves the indexed state unchanged. For a letter followed by a remainder, if the index still lies inside the target, the remaining suffix begins with the character at that index, and the whole word is a prefix exactly when the letter equals that character and the remainder is a prefix of the tail. A matching letter steps to the next index and the inductive hypothesis finishes the remainder. A mismatched letter steps to the sink, which stays the sink, and the word is not a prefix. If the index is already past the end of the target, the step is the sink and the remaining suffix is empty, so the longer word is not a prefix.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import Mathlib.Computability.DFA
import all Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Option
import all Mathlib.Data.Fintype.Option
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA.singleDFA_evalFrom_none

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability


/-- From state `some k`, reading `w` reaches `some (k+|w|)` exactly when `w` is a prefix of the
suffix `σ.drop k` (i.e. `w` continues `σ` from position `k` without diverging); otherwise it dies. -/
theorem singleDFA_evalFrom (σ : List Bool) (w : List Bool) (k : Fin (σ.length + 1)) :
    (singleDFA σ).evalFrom (some k) w =
      if h : w <+: List.drop (k : ℕ) σ
      then some ⟨(k : ℕ) + w.length, by
        have hlen := h.length_le
        rw [List.length_drop] at hlen
        have := k.isLt
        omega⟩
      else none := by
  induction w generalizing k with
  | nil =>
    rw [DFA.evalFrom_nil, dite_eq_left List.nil_prefix]
    simp
  | cons b w ih =>
    rw [DFA.evalFrom_cons]
    show (singleDFA σ).evalFrom ((singleDFA σ).step (some k) b) w = _
    by_cases hk : (k : ℕ) < σ.length
    · have hdrop : List.drop (k : ℕ) σ = σ.get ⟨k, hk⟩ :: List.drop ((k : ℕ) + 1) σ := by
        rw [List.get_eq_getElem]; exact List.drop_eq_getElem_cons hk
      have hcondiff : ((b :: w) <+: List.drop (k : ℕ) σ) ↔ (b = σ.get ⟨k, hk⟩ ∧ w <+: List.drop ((k : ℕ) + 1) σ) := by
        rw [hdrop, List.cons_prefix_cons]
      by_cases hchar : σ.get ⟨k, hk⟩ = b
      · have hstep : (singleDFA σ).step (some k) b = some ⟨(k : ℕ) + 1, by omega⟩ := by
          simp only [singleDFA, Option.bind_some, dite_eq_left hk, ite_eq_left hchar]
        rw [hstep, ih ⟨(k : ℕ) + 1, by omega⟩]
        by_cases hpre : w <+: List.drop ((k : ℕ) + 1) σ
        · rw [dite_eq_left hpre, dite_eq_left (hcondiff.mpr ⟨hchar.symm, hpre⟩)]
          congr 1
          apply Fin.ext
          simp only [List.length_cons]
          omega
        · rw [dite_eq_right hpre, dite_eq_right (fun hc => hpre (hcondiff.mp hc).2)]
      · have hstep : (singleDFA σ).step (some k) b = none := by
          simp only [singleDFA, Option.bind_some, dite_eq_left hk, ite_eq_right hchar]
        rw [hstep, singleDFA_evalFrom_none, dite_eq_right]
        intro hc
        exact hchar (hcondiff.mp hc).1.symm
    · have hstep : (singleDFA σ).step (some k) b = none := by
        simp only [singleDFA, Option.bind_some, dite_eq_right hk]
      rw [hstep, singleDFA_evalFrom_none, dite_eq_right]
      have hd : List.drop (k : ℕ) σ = [] := by
        rw [List.drop_eq_nil_iff]; have := k.isLt; omega
      rw [hd]; exact (by simp : ¬ (b :: w) <+: [])

end Exercise722
end DomainTheory.NeighbourhoodSystems
