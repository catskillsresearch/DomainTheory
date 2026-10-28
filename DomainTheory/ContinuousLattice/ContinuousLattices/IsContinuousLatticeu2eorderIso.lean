module
public import DomainTheory.ContinuousLattice.ContinuousLattices.orderIso_wayBelow
public import Mathlib.Order.BourbakiWitt
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

section Theorem212Transfer

variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]

theorem orderIso (e : A ≃o B) (hB : ContinuousLattice B) :
    ContinuousLattice A := by
  refine { out := ?_ }
  intro y
  refine ⟨fun x hx => hx.le, fun b hb => ?_⟩
  apply e.le_iff_le.mp
  exact (hB.out (e y)).2 fun z hz => by
    have hz' : e.symm z ≪ y := by
      simpa using orderIso_wayBelow e.symm hz
    have := hb hz'
    simpa using e.monotone this

end Theorem212Transfer
end DomainTheory.ContinuousLattice
