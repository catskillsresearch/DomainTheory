module
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice

public import DomainTheory.ContinuousLattice.Constructions.directedOn_finite_sSup_mem
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]

theorem proposition_2_8 [Finite D] : ContinuousLattice D := by
  refine { out := ?_ }
  intro y
  have hopen : ScottOpen (Set.Ici y) := by
    refine ⟨isUpperSet_Ici y, fun S hSne hSdir hmem => ?_⟩
    exact ⟨sSup S, directedOn_finite_sSup_mem (Set.toFinite S) hSne hSdir, hmem⟩
  have hyy : y ≪ y := WayBelow.self_iff_scottOpen_Ici.mpr hopen
  exact ⟨fun x hx => hx.le, fun b hb => hb hyy⟩

end DomainTheory.ContinuousLattice
