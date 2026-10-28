module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Closures.Vapply
public import DomainTheory.DataTypesAsLattices.Closures.Vapply_more
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def Vcomb : Pomega :=
  graph (fun a => graph (fun x => Vapply a x))

namespace Vcomb

theorem app (a : Pomega) :
    funOf Vcomb a = graph (fun x => Vapply a x) :=
  beta (graph_const_isScottContinuous (fun a x => Vapply a x)
    (fun x => Vapply.left_isScottContinuous x)) a

end Vcomb

end DomainTheory.DataTypesAsLattices
