/-ai
The identity combinator is contained in the open-set retract.

Containment of the identity in a graph is equivalent to expansiveness on finite sets. The application formula for the open-set retract rewrites the body at en as the retract applied to en, and that retract is expansive.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
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
