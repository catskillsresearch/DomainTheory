/-ai
After the first step of a path, the state n + 1 symbols along the whole path equals the state n symbols along the remaining path.

Both sides reduce to the same clause of the auxiliary recursion on path states.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instFintypeAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instDecidableEqAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathStateAt_zero

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open scoped Computability

open Sum Set

variable {σ₁ σ₂ : Type}

variable {σ : Type}

section ShortWord

variable {σ : Type} [Fintype σ] {M : NFA Bool σ}

omit [Fintype σ] in
theorem pathStateAt_succ {sMid s' u : σ} {a : Bool} {xs : List Bool}
    (hstep : sMid ∈ M.step s' a) (p' : M.Path sMid u xs) (n : ℕ) (hn : n ≤ xs.length) :
    pathStateAt (.cons sMid s' u a xs hstep p') (n + 1) (Nat.succ_le_succ hn) =
      pathStateAt p' n hn := by
  simp [pathStateAt, pathStateAtAux]

end ShortWord

end Exercise722

end DomainTheory.NeighbourhoodSystems
