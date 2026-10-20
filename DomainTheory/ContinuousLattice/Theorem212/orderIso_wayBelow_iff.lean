/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.ContinuousLattice.Constructions
public import DomainTheory.ContinuousLattice.FunctionSpaces
public import DomainTheory.ContinuousLattice.Theorem212.Basic
public import DomainTheory.ContinuousLattice.Theorem212.orderIso_wayBelow

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set



universe u


section Theorem212Transfer

variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]


/-- Scott's topological way-below relation is invariant under order isomorphism. -/
theorem orderIso_wayBelow_iff (e : A ≃o B) {x y : A} :
    x ≪ y ↔ e x ≪ e y :=
  ⟨orderIso_wayBelow e, fun h => by
    simpa using orderIso_wayBelow e.symm h⟩

end Theorem212Transfer
end DomainTheory.ContinuousLattice
