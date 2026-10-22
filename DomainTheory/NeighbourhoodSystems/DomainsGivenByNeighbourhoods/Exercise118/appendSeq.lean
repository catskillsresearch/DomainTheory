module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic

@[expose] public section

set_option linter.unusedSimpArgs false

namespace DomainTheory.NeighbourhoodSystems

/-- Concatenation of two finite sequences: the first `n1` entries are `X1 0, …, X1 (n1-1)`,
then `X2 0, X2 1, …`. -/
def appendSeq {α : Type*} (X1 : ℕ → Set α) (n1 : ℕ) (X2 : ℕ → Set α) : ℕ → Set α :=
  fun i => if i < n1 then X1 i else X2 (i - n1)

end DomainTheory.NeighbourhoodSystems
