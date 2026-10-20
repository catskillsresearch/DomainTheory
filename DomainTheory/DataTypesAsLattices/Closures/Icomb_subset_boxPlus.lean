module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_graph
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_expansive

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem Icomb_subset_boxPlus {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    Icomb ⊆ boxPlus a b :=
  Icomb_subset_graph.mpr fun n => by
    rw [← boxPlus_app]
    exact boxPlus_expansive ha hb (e n)

end DomainTheory.DataTypesAsLattices
