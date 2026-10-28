module

public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem curry_mid_isScottContinuous (u : Pomega) :
    IsScottContinuous (fun x => graph (fun y => funOf u (pairSeq x y))) :=
  graph_const_isScottContinuous
    (fun x y => funOf u (pairSeq x y))
    (fun y => theorem_1_3 (funOf.isScottContinuous u)
      (pairSeq_isScottContinuous_left y))

end DomainTheory.DataTypesAsLattices
