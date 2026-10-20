/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Formula
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalV
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalSet

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- **The bridge between the two evaluations**: `evalSet` at `n : ℕ` agrees with `evalV` at `n`'s
own bit-sequence `fun i => n.testBit i`. -/
theorem mem_evalSet_iff (n : ℕ) (φ : Formula) :
    n ∈ evalSet φ ↔ evalV (fun i => n.testBit i) φ = true := by
  induction φ with
  | var i => simp [evalSet, evalV]
  | bot => simp [evalSet, evalV]
  | top => simp [evalSet, evalV]
  | neg φ ih => simp [evalSet, evalV, ih]
  | and φ ψ ihφ ihψ => simp [evalSet, evalV, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [evalSet, evalV, ihφ, ihψ]

end DomainTheory.NeighbourhoodSystems
