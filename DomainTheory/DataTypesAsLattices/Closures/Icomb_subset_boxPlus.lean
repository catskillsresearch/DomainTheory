
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Icomb
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Closure
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_graph

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem Icomb_subset_boxPlus {a b : Pomega} (ha : Closure a) (hb : Closure b) :
    Icomb ⊆ boxPlus a b :=
  Icomb_subset_graph.mpr fun n => by
    rw [← boxPlus.app]
    exact boxPlus.expansive ha hb (e n)

end DomainTheory.DataTypesAsLattices
