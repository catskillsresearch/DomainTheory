/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Order.CompleteLattice.Basic
import all Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Directed
import all Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.BridgeTheorems.IsCompactElement
public import DomainTheory.BridgeTheorems.IsAlgebraicLattice

@[expose] public section

/-!
# Algebraic complete lattices → continuous lattices (ideal-completion → 1972)

An **algebraic** complete lattice — every element is the directed supremum of the
compact elements below it — is a continuous lattice in Scott's sense
(`IsContinuousLattice`). Compact elements are way-below anything they lie under,
via Scott-openness of `Set.Ici k`.

This is the classical frontier of this article’s blueprint
(`idealCompletion_to_continuousLattice`): Scott's `≪` is topological.
-/

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice
open scoped DomainTheory.ContinuousLattice

namespace IdealCompletionToContinuousLattice

variable {D : Type*} [CompleteLattice D]


/-- Compactness implies `Set.Ici k` is Scott-open. -/
theorem scottOpen_Ici_of_compact {k : D} (hk : IsCompactElement k) :
    ScottOpen (Set.Ici k) := by
  refine ⟨isUpperSet_Ici k, fun S hS hSdir hmem => ?_⟩
  obtain ⟨s, hsS, hks⟩ := hk hS hSdir (Set.mem_Ici.1 hmem)
  exact ⟨s, hsS, Set.mem_Ici.2 hks⟩

/-- Compact elements are way below anything above them. -/
theorem compact_wayBelow {k y : D} (hk : IsCompactElement k) (hky : k ≤ y) : k ≪ y :=
  ⟨Set.Ici k, scottOpen_Ici_of_compact hk, Set.mem_Ici.2 hky, subset_rfl⟩


/-- **Blueprint:** algebraic complete lattice ⇒ continuous lattice (Scott Def. 2.3). -/
theorem isContinuousLattice_of_algebraic (hA : IsAlgebraicLattice D) :
    IsContinuousLattice D := by
  intro y
  obtain ⟨hne, hdir, hsup⟩ := hA y
  refine ⟨?_, fun z hz => ?_⟩
  · -- y is an upper bound of `{x | x ≪ y}`
    intro x hx
    exact hx.le
  · -- any upper bound of the way-belows is ≥ y
    -- every compact ≤ y is ≪ y, hence ≤ z
    have hle : sSup {x : D | IsCompactElement x ∧ x ≤ y} ≤ z := by
      refine sSup_le fun x hx => ?_
      exact hz (compact_wayBelow hx.1 hx.2)
    exact hsup ▸ hle

end IdealCompletionToContinuousLattice

/-- Blueprint name. -/
abbrev idealCompletion_to_continuousLattice {D : Type*} [CompleteLattice D]
    (hA : IdealCompletionToContinuousLattice.IsAlgebraicLattice D) :
    IsContinuousLattice D :=
  IdealCompletionToContinuousLattice.isContinuousLattice_of_algebraic hA

end DomainTheory.BridgeTheorems
