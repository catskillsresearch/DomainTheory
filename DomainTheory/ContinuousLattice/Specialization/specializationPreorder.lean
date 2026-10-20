module

public import DomainTheory.ContinuousLattice.WayBelow
public import Mathlib.Topology.Inseparable
import all Mathlib.Topology.Inseparable
public import Mathlib.Topology.Separation.Basic
import all Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Order.ScottTopology
import all Mathlib.Topology.Order.ScottTopology
public import Mathlib.Order.DirSupClosed
import all Mathlib.Order.DirSupClosed
public import DomainTheory.ContinuousLattice.Specialization.SpecializationLe

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]

instance specializationPreorder : Preorder X where
  le := SpecializationLe
  le_refl x := fun _ _ hx => hx
  le_trans x y z hxy hyz U hU hxU := hyz U hU (hxy U hU hxU)

end DomainTheory.ContinuousLattice
