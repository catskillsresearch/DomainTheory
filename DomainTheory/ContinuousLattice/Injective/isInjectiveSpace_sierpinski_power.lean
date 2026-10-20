/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import DomainTheory.ContinuousLattice.Injective.Basic
import DomainTheory.ContinuousLattice.Injective.proposition_1_2
import DomainTheory.ContinuousLattice.Injective.proposition_1_3



open Topology TopologicalSpace

universe u v w


theorem isInjectiveSpace_sierpinski_power (ι : Type w) :
    IsInjectiveSpace.{u} (ι → Prop) :=
  proposition_1_3 (fun (_ : ι) => Prop) (fun _ => proposition_1_2)

