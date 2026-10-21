/-ai
The universe combinator applied to a equals the graph of x ↦ V(a)(x).

For each x the map a ↦ V(a)(x) is Scott continuous, so the inner graph is Scott continuous in a. The β rule for a continuous body therefore evaluates the outer graph at a as that inner graph.
ai-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Vapply_left_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem Vcomb_app (a : Pomega) :
    funOf Vcomb a = graph (fun x => Vapply a x) :=
  beta (graph_const_isScottContinuous (fun a x => Vapply a x)
    (fun x => Vapply_left_isScottContinuous x)) a

end DomainTheory.DataTypesAsLattices
