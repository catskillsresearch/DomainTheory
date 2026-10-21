/-ai
pathStateAtAux is the state reached after reading n symbols along a path, for n at most the length of the word. The empty path contributes its state at position zero, and a positive position on the empty path is impossible. A path that begins with one step contributes its starting state at position zero, and at a later position continues on the remaining path with the index decreased by one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

variable {σ : Type}

variable {σ : Type} [Fintype σ] {M : NFA Bool σ}

/-- State after reading the first `n` symbols along a concrete path (`n ≤ x.length`). -/
def pathStateAtAux {s t : σ} {x : List Bool} : M.Path s t x → ∀ n, n ≤ x.length → σ
  | .nil s, 0, _ => s
  | .nil _, n + 1, hn => (Nat.not_succ_le_zero n hn).elim
  | .cons _ s' _ _ _ _ p', 0, _ => s'
  | .cons _ _ _ _ _ _ p', n + 1, hn =>
      pathStateAtAux p' n (Nat.le_of_succ_le_succ hn)

end Exercise722

end DomainTheory.NeighbourhoodSystems
