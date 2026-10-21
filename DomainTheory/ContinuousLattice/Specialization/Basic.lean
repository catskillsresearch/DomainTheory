/-ai
This file gathers and re-exports the way-below relation, inseparability and separation, the Scott topology, directed-supremum closure, the specialization order, the Scott topological space, monotone nets, Scott convergence, and the specialization preorder. It is the setting for the opening of Scott's section 2: the specialization order on a T0-space and the induced Scott topology on a complete lattice, with Proposition 2.1 split into its two directions and the convergence-from-below direction recorded separately.
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
public import DomainTheory.ContinuousLattice.Specialization.SpecializationLe
public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import DomainTheory.ContinuousLattice.Specialization.IsMonotoneNet
public import DomainTheory.ContinuousLattice.Specialization.ScottConvergesTo
public import DomainTheory.ContinuousLattice.Specialization.specializationPreorder

@[expose] public section

/-!
# Specialization order and Scott topology (Scott 1972, §2 opening)

Scott's §2 begins with the specialization order on a `T₀`-space and the induced (Scott)
topology on a complete lattice. Proposition 2.1 (monotone nets and least upper bounds) is
split into its two directions; the convergence-to-below direction is the mathematically
heavier half and is recorded as `proposition_2_1_of_le`.
-/

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]

/-! ### Specialization order -/


/-! ### Scott topology from `ScottOpen` -/


/-! ### Monotone nets and Proposition 2.1 -/

variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]


variable {x : ι → D} {L y : D}
end DomainTheory.ContinuousLattice
