/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.InverseLimits
import Mathlib.Order.Hom.Basic
import Mathlib.Topology.Homeomorph.Defs
import DomainTheory.ContinuousLattice.FunctionSpaceTower.Basic


namespace DomainTheory.ContinuousLattice

universe u


attribute [instance] CLat.str









section Conj

open Set

variable {Y Z W : Type u} [CompleteLattice Y] [CompleteLattice Z] [CompleteLattice W]


theorem conjMapFun_apply (post : ScottMap Y Z) (pre : ScottMap W Y) (f : ScottMap Y Y) (x : W) :
    conjMapFun post pre f x = post (f (pre x)) := rfl

end Conj
end DomainTheory.ContinuousLattice
