module
public import DomainTheory.ContinuousLattice.ContinuousLattices.scottOpen_preimage_orderIso
public import Mathlib.Order.BourbakiWitt
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

section Theorem212Transfer

variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]

theorem orderIso_wayBelow (e : A ≃o B) {x y : A} (h : x ≪ y) :
    e x ≪ e y := by
  obtain ⟨U, hU, hyU, hUsub⟩ := h
  refine ⟨e.symm ⁻¹' U, scottOpen_preimage_orderIso e.symm hU, ?_, ?_⟩
  · simpa using hyU
  · intro z hz
    have hxz : x ≤ e.symm z := Set.mem_Ici.1 (hUsub hz)
    exact Set.mem_Ici.2 (by simpa using (e.le_iff_le.mpr hxz))

end Theorem212Transfer
end DomainTheory.ContinuousLattice
