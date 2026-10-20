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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.vars
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.mem_evalSet_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.evalV_eq_of_agree
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.exists_bitsOf_agree
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.SemanticEquiv
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.formulaSetoid

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- **The one substantive lemma**: semantic equivalence (quantifying over *all* valuations) agrees
with `evalSet`-equality (which only ever "tests" the countably many bit-derived valuations) —
because a formula only mentions finitely many variables, any valuation can be swapped for a
matching bit-derived one on the (finite) variables that actually occur. -/
theorem semanticEquiv_iff_evalSet_eq {φ ψ : Formula} :
    SemanticEquiv φ ψ ↔ evalSet φ = evalSet ψ := by
  constructor
  · intro h
    ext n
    rw [mem_evalSet_iff, mem_evalSet_iff, h]
  · intro h v
    obtain ⟨n, hn⟩ := exists_bitsOf_agree (vars φ ∪ vars ψ) v
    have h1 : evalV v φ = evalV (fun i => n.testBit i) φ :=
      evalV_eq_of_agree fun i hi => (hn i (Finset.mem_union_left _ hi)).symm
    have h2 : evalV v ψ = evalV (fun i => n.testBit i) ψ :=
      evalV_eq_of_agree fun i hi => (hn i (Finset.mem_union_right _ hi)).symm
    have hiff : evalV (fun i => n.testBit i) φ = true ↔ evalV (fun i => n.testBit i) ψ = true := by
      rw [← mem_evalSet_iff, ← mem_evalSet_iff, h]
    rw [h1, h2]
    rcases hφ : evalV (fun i => n.testBit i) φ with - | - <;>
      rcases hψ : evalV (fun i => n.testBit i) ψ with - | - <;> simp_all

end DomainTheory.NeighbourhoodSystems
