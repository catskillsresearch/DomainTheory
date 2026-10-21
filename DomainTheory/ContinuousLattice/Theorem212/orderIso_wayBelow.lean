/-ai
An order isomorphism preserves the way-below relation.

A Scott-open neighbourhood of the larger element contained in the principal upset of the smaller element pulls back along the inverse isomorphism to a Scott-open neighbourhood of the image of the larger element. A point of that preimage has inverse above the smaller element, and the order isomorphism sends that inequality to the image of the smaller element below the point.
ai-/
module

public import DomainTheory.ContinuousLattice.Constructions
public import DomainTheory.ContinuousLattice.FunctionSpaces
public import DomainTheory.ContinuousLattice.Theorem212.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set



universe u


section Theorem212Transfer

variable {A B : Type u} [latticeA : CompleteLattice A] [latticeB : CompleteLattice B]


/-- Order isomorphisms preserve Scott's topological way-below relation. -/
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
