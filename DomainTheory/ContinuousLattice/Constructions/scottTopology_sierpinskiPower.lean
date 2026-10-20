/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.MilnerCorrection
import DomainTheory.ContinuousLattice.ScottMaps
import DomainTheory.ContinuousLattice.Injective
import Mathlib.Order.Preorder.Finite
import DomainTheory.ContinuousLattice.Constructions.Basic
import DomainTheory.ContinuousLattice.Constructions.proposition_2_9_b
import DomainTheory.ContinuousLattice.Constructions.isContinuousLattice_prop
import DomainTheory.ContinuousLattice.Constructions.scottTopology_prop


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]







/-- The Scott topology on a power `ι → 𝕆` of the Sierpiński space coincides with the product
(= Sierpiński power) topology. Combine Proposition 2.9(b) (the Scott topology of a product is the
product of the factors' Scott topologies) with `scottTopology_prop` (each factor's Scott topology
is the Sierpiński topology). -/
theorem scottTopology_sierpinskiPower (ι : Type*) :
    (scottTopologicalSpace : TopologicalSpace (ι → Prop)) =
      (inferInstance : TopologicalSpace (ι → Prop)) := by
  rw [proposition_2_9_b (fun _ => Prop) (fun _ => isContinuousLattice_prop)]
  show (@Pi.topologicalSpace ι (fun _ => Prop) (fun _ => scottTopologicalSpace)) =
    @Pi.topologicalSpace ι (fun _ => Prop) (fun _ => sierpinskiSpace)
  congr 1
  funext _
  exact scottTopology_prop

end DomainTheory.ContinuousLattice
