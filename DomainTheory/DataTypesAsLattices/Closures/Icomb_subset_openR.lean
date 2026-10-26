
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Retracts.openR
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_graph
public import DomainTheory.DataTypesAsLattices.Closures.openR_app
public import DomainTheory.DataTypesAsLattices.Closures.openR_expansive

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Icomb_subset_openR : Icomb ⊆ openR :=
  Icomb_subset_graph.mpr fun n => by
    rw [← openR_app]
    exact openR_expansive (e n)

end DomainTheory.DataTypesAsLattices
