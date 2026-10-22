module
public import DomainTheory.ContinuousLattice.ContinuousLattices.orderIso_wayBelow
public import Mathlib.Order.BourbakiWitt
public import DomainTheory.ContinuousLattice.WayBelow.Basic.notation5
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic


@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set


universe u


section Theorem212Transfer

variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]


/-- Scott's topological way-below relation is invariant under order isomorphism. -/
theorem orderIso_wayBelow_iff (e : A ≃o B) {x y : A} :
    x ≪ y ↔ e x ≪ e y :=
  ⟨orderIso_wayBelow e, fun h => by
    simpa using orderIso_wayBelow e.symm h⟩

end Theorem212Transfer
end DomainTheory.ContinuousLattice
