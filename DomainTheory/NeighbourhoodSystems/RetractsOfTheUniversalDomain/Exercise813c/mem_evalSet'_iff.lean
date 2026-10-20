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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_genPoint
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.mem_box
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.evalSet'

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

/-- Cantor space's own points already *are* valuations, so this bridge is definitional-level
simple: no bit-encoding step is needed (contrast `8.13(b)`'s `mem_evalSet_iff`). -/
theorem mem_evalSet'_iff (x : ℕ → Bool) (φ : Formula) :
    x ∈ evalSet' φ ↔ evalV x φ = true := by
  induction φ with
  | var i => simp [evalSet', evalV]
  | bot => simp [evalSet', evalV]
  | top => simp [evalSet', evalV]
  | neg φ ih => simp [evalSet', evalV, ih]
  | and φ ψ ihφ ihψ => simp [evalSet', evalV, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [evalSet', evalV, ihφ, ihψ]

end DomainTheory.NeighbourhoodSystems
