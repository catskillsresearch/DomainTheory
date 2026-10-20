/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- Given any (finite) target set of variables and any valuation `v`, some `n : ℕ` matches `v` on
exactly that set — witnessed directly via `bitmaskOf` (`Exercise813a.lean`). -/
theorem exists_bitsOf_agree (S : Finset ℕ) (v : ℕ → Bool) :
    ∃ n : ℕ, ∀ i ∈ S, n.testBit i = v i := by
  refine ⟨bitmaskOf (S.filter (fun i => v i)), fun i hi => ?_⟩
  have key : (bitmaskOf (S.filter (fun i => v i))).testBit i = true ↔ v i = true := by
    rw [testBit_bitmaskOf]; simp [Finset.mem_filter, hi]
  rcases hv : v i with - | - <;> rcases hn : (bitmaskOf (S.filter (fun i => v i))).testBit i
    with - | - <;> simp_all

end DomainTheory.NeighbourhoodSystems
