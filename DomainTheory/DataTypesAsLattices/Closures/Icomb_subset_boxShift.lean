
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_graph
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_app
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_expansive

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Icomb_subset_boxShift {a : Pomega} (ha : Closure a) :
    Icomb ⊆ boxShift a :=
  Icomb_subset_graph.mpr fun n => by
    rw [← boxShift_app]
    exact boxShift_expansive ha (e n)

end DomainTheory.DataTypesAsLattices
