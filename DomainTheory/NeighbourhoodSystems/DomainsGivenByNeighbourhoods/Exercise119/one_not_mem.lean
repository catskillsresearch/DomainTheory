/-ai
The singleton of the middle token is not a neighbourhood.

If it were a neighbourhood, it would equal the master or one of the two overlapping neighbourhoods. The master and the first overlapping neighbourhood contain the first token, and the second contains the last token, and none of those tokens lies in the singleton.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise119.Basic

@[expose] public section


set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems.Exercise119

open DomainTheory.NeighbourhoodSystems


/-- `{1}` is not a neighbourhood (it is neither `Δ`, `{0,1}`, nor `{1,2}`). -/
theorem one_not_mem : ¬ mem ({1} : Set Tok) := by
  intro h
  rcases (mem_iff _).mp h with h | h | h
  · have h0 : (0 : Tok) ∈ master := by simp [master]
    rw [← h] at h0; simp at h0
  · have h0 : (0 : Tok) ∈ a := by simp [a]
    rw [← h] at h0; simp at h0
  · have h2 : (2 : Tok) ∈ b := by simp [b]
    rw [← h] at h2; simp at h2

end DomainTheory.NeighbourhoodSystems.Exercise119
