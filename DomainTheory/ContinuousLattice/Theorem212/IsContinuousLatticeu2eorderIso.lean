/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.Constructions
import DomainTheory.ContinuousLattice.FunctionSpaces
import DomainTheory.ContinuousLattice.Theorem212.Basic
import DomainTheory.ContinuousLattice.Theorem212.orderIso_wayBelow


namespace DomainTheory.ContinuousLattice

open Topology Set



universe u


section Theorem212Transfer

variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]


/-- Continuous-lattice structure transfers across an order isomorphism. -/
theorem IsContinuousLattice.orderIso (e : A ≃o B) (hB : IsContinuousLattice B) :
    IsContinuousLattice A := by
  intro y
  refine ⟨fun x hx => hx.le, fun b hb => ?_⟩
  apply e.le_iff_le.mp
  exact (hB (e y)).2 fun z hz => by
    have hz' : e.symm z ≪ y := by
      simpa using orderIso_wayBelow e.symm hz
    have := hb hz'
    simpa using e.monotone this

end Theorem212Transfer
end DomainTheory.ContinuousLattice
