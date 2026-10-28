module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]

theorem scottOpen_wayBelow (x : D) : ScottOpen {z | x ≪ z} := by
  refine ⟨fun a b hab ha => ha.trans_le hab, fun S hS hSdir hmem => ?_⟩
  obtain ⟨U, hU, hsupU, hsub⟩ := hmem
  obtain ⟨s, hsS, hsU⟩ := hU.2 hS hSdir hsupU
  exact ⟨s, hsS, ⟨U, hU, hsU, hsub⟩⟩

end DomainTheory.ContinuousLattice
