module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.succSet
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def interStep (f : Pomega) : Pomega :=
  graph (fun x => graph (fun y =>
    condSet x (condSet y (ofNat 0) botElem)
      (succSet (funOf (funOf f (predSet x)) (predSet y)))))

namespace interStep

theorem isScottContinuous :
    IsScottContinuous interStep := by
  refine graph_const_isScottContinuous
    (fun f x => graph (fun y =>
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf f (predSet x)) (predSet y))))) ?_
  intro x
  refine graph_const_isScottContinuous
    (fun f y =>
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf f (predSet x)) (predSet y)))) ?_
  intro y
  refine theorem_1_3
    (condSet.isScottContinuous_right x (condSet y (ofNat 0) botElem)) ?_
  refine theorem_1_3 succSet.isScottContinuous ?_
  exact theorem_1_3
    (f := fun t => funOf t (predSet y))
    (g := fun f => funOf f (predSet x))
    (funOf.isScottContinuous_left (predSet y))
    (funOf.isScottContinuous_left (predSet x))

end interStep

end DomainTheory.DataTypesAsLattices
