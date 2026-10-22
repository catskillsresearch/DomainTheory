module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.Constructions.directedOn_finite_sSup_mem
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Basic.Finite.Defs
public import DomainTheory.ContinuousLattice.WayBelow.wayBelow_self_iff_scottOpen_Ici
public import DomainTheory.ContinuousLattice.WayBelow.WayBelowu2ele
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]

/-- **Scott 1972, Proposition 2.8.** A finite lattice is a continuous lattice. In a finite
lattice every principal up-set `Set.Ici y` is Scott-open (a non-empty directed set is finite,
so it attains its supremum), hence `y ≪ y`; therefore `y` is the supremum of `{x | x ≪ y}`. -/
theorem proposition_2_8 [Finite D] : ContinuousLattice D := by
  refine { out := ?_ }
  intro y
  have hopen : ScottOpen (Set.Ici y) := by
    refine ⟨isUpperSet_Ici y, fun S hSne hSdir hmem => ?_⟩
    exact ⟨sSup S, directedOn_finite_sSup_mem (Set.toFinite S) hSne hSdir, hmem⟩
  have hyy : y ≪ y := wayBelow_self_iff_scottOpen_Ici.mpr hopen
  exact ⟨fun x hx => hx.le, fun b hb => hb hyy⟩

end DomainTheory.ContinuousLattice
