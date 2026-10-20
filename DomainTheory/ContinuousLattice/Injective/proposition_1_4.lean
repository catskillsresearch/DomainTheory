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
import DomainTheory.ContinuousLattice.Injective.IsInjectiveSpaceu2eof_retract



open Topology TopologicalSpace

universe u v w


theorem proposition_1_4 {D : Type v} {D' : Type v} [TopologicalSpace D] [TopologicalSpace D']
    (hD : IsInjectiveSpace.{u} D) (s : C(D', D)) (r : C(D, D')) (hrs : ∀ d, r (s d) = d) :
    IsInjectiveSpace.{u} D' :=
  IsInjectiveSpace.of_retract hD s r hrs

