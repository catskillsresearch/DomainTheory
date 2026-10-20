/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition79
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition710.PowerDomain_master

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

variable (P : ComputablePresentation V)

/-- If `(a, b)` is *inconsistent* (no `𝒟`-neighbourhood below `X_a ∩ X_b`) then `↓X_a ∩ ↓X_b = ∅`. -/
theorem upSet_inter_eq_empty_of_not_cons {a b : ℕ}
    (h : ¬ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    V.upSet (P.X a) ∩ V.upSet (P.X b) = ∅ := by
  rw [V.upSet_inter]
  ext Z
  simp only [mem_upSet, Set.mem_empty_iff_false, iff_false, not_and]
  intro hZmem hZsub
  obtain ⟨n, hn⟩ := P.surj hZmem
  exact h ⟨n, by rw [hn]; exact hZsub⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
