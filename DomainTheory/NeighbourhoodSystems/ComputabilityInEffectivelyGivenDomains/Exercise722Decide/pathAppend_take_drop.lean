/-ai
pathAppend_take_drop splits a path at a position n not past the end of the word into a prefix path, a suffix path, and the state at the cut. On the empty path the cut is at zero and both pieces are trivial. On a one-step path, a cut at zero leaves an empty prefix and the original path as the suffix; a later cut recurses on the continuation and rebuilds the prefix by the same first step, with the state at the cut identified by the successor equation for states along a path.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.PathSplit
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instFintypeAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.instDecidableEqAutState
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathStateAt_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathStateAt_succ

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

noncomputable def pathAppend_take_drop {s t : σ} {x : List Bool} (p : M.Path s t x) (n : ℕ)
    (hn : n ≤ x.length) : PathSplit p n hn := by
  revert n hn
  induction p with
  | nil s =>
    intro n hn
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst hn0
    exact { u := s, hp := .nil s, ht := .nil s, hu := by rfl }
  | cons sMid s' u a xs hstep p' ih =>
    intro n hn
    cases n with
    | zero =>
      exact { u := s', hp := .nil s', ht := .cons sMid s' u a xs hstep p', hu := by rfl }
    | succ n' =>
      have hn' : n' ≤ xs.length := by simpa [List.length_cons] using hn
      have split := ih n' hn'
      exact {
        u := split.u
        hp := .cons sMid s' split.u a (xs.take n') hstep split.hp
        ht := split.ht
        hu := by rw [pathStateAt_succ hstep p' n' hn']; exact split.hu
      }

end ShortWord

end Exercise722

end DomainTheory.NeighbourhoodSystems
