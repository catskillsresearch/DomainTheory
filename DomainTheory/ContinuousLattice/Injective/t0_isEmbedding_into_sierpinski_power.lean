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
import DomainTheory.ContinuousLattice.Injective.proposition_1_5



open Topology TopologicalSpace

universe u v w


theorem t0_isEmbedding_into_sierpinski_power (X : Type u) [TopologicalSpace X] [T0Space X] :
    IsEmbedding (productOfMemOpens X) :=
  (proposition_1_5 X).2

