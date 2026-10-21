/-ai
If a is a closure, the identity combinator is contained in the shift of a.

Containment of the identity in a graph is equivalent to expansiveness on finite sets. The application formula for the shift rewrites the body at en as the shift applied to en, and the shift of a closure is expansive.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Icomb_subset_graph
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_app
public import DomainTheory.DataTypesAsLattices.Closures.boxShift_expansive

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem Icomb_subset_boxShift {a : Pomega} (ha : IsClosure a) :
    Icomb ⊆ boxShift a :=
  Icomb_subset_graph.mpr fun n => by
    rw [← boxShift_app]
    exact boxShift_expansive ha (e n)

end DomainTheory.DataTypesAsLattices
