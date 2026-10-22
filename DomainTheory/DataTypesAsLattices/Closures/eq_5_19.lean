/-ai
Applying the closure combinator V twice to a set a equals applying it once.

The graph of V(a) is a closure. The characterization of closures says that this graph is fixed by V. The application law for V identifies the single application with that graph, so the fixed-point equation is the claim.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.Vcomb_app
public import DomainTheory.DataTypesAsLattices.Closures.theorem_5_5_iff
public import DomainTheory.DataTypesAsLattices.Closures.Vapply_graph_isClosure

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem eq_5_19 (a : Pomega) :
    funOf Vcomb (funOf Vcomb a) = funOf Vcomb a := by
  have hcl := Vapply_graph_isClosure a
  have hfix := (theorem_5_5_iff (graph (fun x => Vapply a x))).mp hcl
  have ha : funOf Vcomb a = graph (fun x => Vapply a x) := Vcomb_app a
  rw [ha]
  exact hfix

end DomainTheory.DataTypesAsLattices
