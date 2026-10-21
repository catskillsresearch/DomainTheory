/-ai
The state zero symbols along a path is the path's starting state.

Case on the word. On the empty word the path is empty and the definitions reduce. On a nonempty word the path begins with a step, and the zero clause of the auxiliary recursion is the starting state.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instFintypeAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instDecidableEqAutState

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
@[simp] theorem pathStateAt_zero {s t : σ} {x : List Bool} (p : M.Path s t x) :
    pathStateAt p 0 (Nat.zero_le _) = s := by
  cases x with
  | nil =>
    cases p; simp [pathStateAt, pathStateAtAux]
  | cons a xs =>
    cases p with
    | cons _ s' _ _ _ _ _ => simp [pathStateAt, pathStateAtAux]

end ShortWord

end Exercise722

end DomainTheory.NeighbourhoodSystems
