
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.boxShift
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_graph

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Icomb_subset_boxShift {a : Pomega} (ha : Closure a) :
    Icomb ⊆ boxShift a :=
  Icomb_subset_graph.mpr fun n => by
    rw [← boxShift.app]
    exact boxShift.expansive ha (e n)

theorem boxShift.isClosure {a : Pomega} (ha : Closure a) :
    Closure (boxShift a) :=
  ⟨⟨Icomb_subset_boxShift ha, boxShift.isRetract ha.out.2⟩⟩

end DomainTheory.DataTypesAsLattices
