/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import DomainTheory.ContinuousLattice.FunctionSpaces.Basic


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']







theorem specializationLe_generateOpen (f g : C(X, Y)) (hfg : ∀ x, SpecializationLe (f x) (g x))
    {V : Set (C(X, Y))} (hV : GenerateOpen (scottFunctionEvalSubbasis X Y) V) (hf : f ∈ V) :
    g ∈ V :=
  match hV with
  | .basic W hW => by
    obtain ⟨x, U, hU, rfl⟩ := hW
    exact hfg x U hU hf
  | .univ => hf
  | .inter s t hs ht => by
    rcases hf with ⟨hfs, hft⟩
    exact Set.mem_inter (specializationLe_generateOpen f g hfg hs hfs)
      (specializationLe_generateOpen f g hfg ht hft)
  | .sUnion S hS => by
    obtain ⟨W, hWS, hfW⟩ := Set.mem_sUnion.mp hf
    exact Set.mem_sUnion.mpr ⟨W, hWS, specializationLe_generateOpen f g hfg (hS W hWS) hfW⟩

end DomainTheory.ContinuousLattice
