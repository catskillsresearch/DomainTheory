/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public meta import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular.Basic

@[expose] public section

/-!
# Exercise 7.22 — bounded word enumeration for emptiness search

Lists every `List Bool` of length at most `n` (`wordsUpTo n`), and provides `anyMatchesB` to test
whether any word in a finite list is accepted by the `matchesB` matcher. The characterisation
`mem_wordsUpTo` is the length bound used later for pumping-based short-word search (Session C4).
-/

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

/-- Every word over `{false,true}` of length at most `n`, listed without duplicates. -/
def wordsUpTo : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    (wordsUpTo n) ++ (wordsUpTo n).flatMap fun w => [[false] ++ w, [true] ++ w]

/-- True iff some word in `ws` is accepted by `matchesB e`. -/
def anyMatchesB (e : SExpr) (ws : List (List Bool)) : Bool := ws.any (matchesB e)

#eval anyMatchesB .sigma (wordsUpTo 0) -- should be `true` (the empty word lies in Σ)
end Exercise722
end DomainTheory.NeighbourhoodSystems
