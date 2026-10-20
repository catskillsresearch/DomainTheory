/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module


public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722DFA
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Cat
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words

@[expose] public section

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

def pathStateAt {s t : σ} {x : List Bool} (p : M.Path s t x) (n : ℕ) (hn : n ≤ x.length) : σ :=
  pathStateAtAux p n hn

structure PathSplit {s t : σ} {x : List Bool} (p : M.Path s t x) (n : ℕ) (hn : n ≤ x.length) where
  u : σ
  hp : M.Path s u (x.take n)
  ht : M.Path u t (x.drop n)
  hu : pathStateAt p n hn = u

end Exercise722
end DomainTheory.NeighbourhoodSystems
