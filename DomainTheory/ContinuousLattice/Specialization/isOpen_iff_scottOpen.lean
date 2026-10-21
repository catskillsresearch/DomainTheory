/-ai
A set is open in the Scott topological space if and only if it is Scott-open.

Scott-openness rewrites as the conjunction of being an upper set and being inaccessible by directed suprema, and the Scott topological space is the Scott topology of the whole universe. That topology is a Scott topology by the reflexivity of its defining equality. Mathlib's criterion of openness in a Scott topology is then the same conjunction on the universe, which matches the rewritten form.
ai-/
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
public import DomainTheory.ContinuousLattice.Specialization.Basic
public import DomainTheory.ContinuousLattice.Specialization.ScottOpen_iff_dirSupInacc

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]


theorem isOpen_iff_scottOpen {U : Set D} : @IsOpen D scottTopologicalSpace U ↔ ScottOpen U := by
  rw [ScottOpen_iff_dirSupInacc, scottTopologicalSpace]
  have hinst : @IsScott D univ _ (Topology.scott D univ) :=
    @IsScott.mk D univ _ (Topology.scott D univ) rfl
  simpa [dirSupInaccOn_univ] using
    @IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn D univ _ (Topology.scott D univ) U hinst

end DomainTheory.ContinuousLattice
