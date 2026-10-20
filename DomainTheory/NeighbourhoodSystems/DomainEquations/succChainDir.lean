module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise617
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_zero
public import DomainTheory.NeighbourhoodSystems.DomainEquations.consSeq_succ
public import DomainTheory.NeighbourhoodSystems.DomainEquations.component_bot
public import DomainTheory.NeighbourhoodSystems.DomainEquations.chain_le_of_succ

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Exercise618

variable {α : Type*} {V : NeighborhoodSystem α}

/-- Directedness of a successor-increasing chain. -/
theorem succChainDir {β : Type*} {W : NeighborhoodSystem β} (a : ℕ → W.Element)
    (h : ∀ n, a n ≤ a (n + 1)) : ∀ i j, ∃ l, a i ≤ a l ∧ a j ≤ a l :=
  fun i j => ⟨max i j, chain_le_of_succ h (le_max_left i j), chain_le_of_succ h (le_max_right i j)⟩

end Exercise618

end DomainTheory.NeighbourhoodSystems
