/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
import all Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
import all Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
import all Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.evalSet'

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

theorem generatedBy_iff_exists_evalSet' {Y : Set (ℕ → Bool)} :
    GeneratedBy genPoint Y ↔ ∃ φ : Formula, evalSet' φ = Y := by
  constructor
  · intro h
    induction h with
    | of i => exact ⟨.var i, rfl⟩
    | univ => exact ⟨.top, rfl⟩
    | @inter X Y _ _ ih1 ih2 =>
      obtain ⟨φ, rfl⟩ := ih1; obtain ⟨ψ, rfl⟩ := ih2
      exact ⟨.and φ ψ, rfl⟩
    | @union X Y _ _ ih1 ih2 =>
      obtain ⟨φ, rfl⟩ := ih1; obtain ⟨ψ, rfl⟩ := ih2
      exact ⟨.or φ ψ, rfl⟩
    | @compl X _ ih =>
      obtain ⟨φ, rfl⟩ := ih
      exact ⟨.neg φ, rfl⟩
  · rintro ⟨φ, rfl⟩
    induction φ with
    | var i => exact GeneratedBy.of i
    | bot => simpa [evalSet'] using GeneratedBy.univ.compl
    | top => exact GeneratedBy.univ
    | neg φ ih => exact ih.compl
    | and φ ψ ihφ ihψ => exact ihφ.inter ihψ
    | or φ ψ ihφ ihψ => exact ihφ.union ihψ

end DomainTheory.NeighbourhoodSystems
