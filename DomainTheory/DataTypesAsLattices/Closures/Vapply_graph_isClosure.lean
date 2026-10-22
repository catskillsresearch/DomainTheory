/-ai
The graph of x ↦ V(a)(x) is a closure for every a. Scott's equation (5.19) records that the universe of this closure is the closure itself.

The identity is contained in the graph because equation (5.16) puts each finite set en inside V(a)(en). For the retract equation, Theorem 1.2(i), using Scott continuity of V(a) in its argument, recovers the map from its graph, and equation (5.17) says that this map is idempotent, so the graph equals the graph of its own double application.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_16
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_17
public import DomainTheory.DataTypesAsLattices.Closures.Vapply_right_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, (5.19).** `V(a)` is always a closure, so `V(V(a)) = V(a)`. -/
theorem Vapply_graph_isClosure (a : Pomega) :
    IsClosure (graph (fun x => Vapply a x)) := by
  constructor
  · intro p hp
    rcases hp with ⟨n, m, rfl, hm⟩
    exact ⟨n, m, rfl, eq_5_16 a (e n) hm⟩
  · change graph (fun x => Vapply a x) =
        graph (fun x =>
          funOf (graph (fun z => Vapply a z))
            (funOf (graph (fun z => Vapply a z)) x))
    apply graph_ext
    intro x
    have happ : funOf (graph (fun z => Vapply a z)) =
        fun z => Vapply a z :=
      theorem_1_2_i (Vapply_right_isScottContinuous a)
    simpa [happ] using (eq_5_17 a x).symm

end DomainTheory.DataTypesAsLattices
