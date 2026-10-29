module

public import DomainTheory.ContinuousLattice.FunctionSpaces.fix_preservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic.isLUB_sSup
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Finset.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

abbrev ScottFunctionSpace (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :=
  C(X, Y)

abbrev ScottC (D D' : Type*) [CompleteLattice D] [CompleteLattice D'] :=
  @ContinuousMap D D' scottTopologicalSpace scottTopologicalSpace

namespace IsContinuousLatticeRetraction

end IsContinuousLatticeRetraction

section Proposition310

open Finset

namespace IsContinuousLatticeProjection

theorem directedOn_wayBelow (a : D) : DirectedOn (· ≤ ·) { z | z ≪ a } := by
  intro p hp q hq
  exact ⟨p ⊔ q, WayBelow.sup hp hq, le_sup_left, le_sup_right⟩

end IsContinuousLatticeProjection

variable {i : D → D'}

end Proposition310

namespace Proposition313

end Proposition313
namespace Proposition314
@[simp] theorem fix.map_apply (f : ScottMap D D) : (fix.map f : D) = Proposition314.fix f := rfl

end Proposition314

end DomainTheory.ContinuousLattice
