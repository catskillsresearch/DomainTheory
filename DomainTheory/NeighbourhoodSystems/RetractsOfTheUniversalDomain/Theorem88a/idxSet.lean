module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.splitChoice_isSplitSpec
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import Mathlib.Basic.Countable.Defs
import all Mathlib.Basic.Countable.Defs

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

section Reencode

variable (e : ℕ → Set α)

/-- **Scott's `↓(e n)`, reindexed over `ℕ`**: the set of indices `m` whose neighbourhood `e m` sits
below `e n`. This is `D†`'s replacement for `e n` itself. -/
def idxSet (n : ℕ) : Set ℕ := {m | e m ⊆ e n}

end Reencode

end DomainTheory.NeighbourhoodSystems
