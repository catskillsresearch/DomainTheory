
module

public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem tensorR_right_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun b => tensorR a b) :=
  graph_const_isScottContinuous
    (fun b u =>
      pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1))))
    (fun u =>
      theorem_1_3
        (f := fun y => pairSeq (funOf a (funOf u (ofNat 0))) y)
        (g := fun b => funOf b (funOf u (ofNat 1)))
        (pairSeq_isScottContinuous_right (funOf a (funOf u (ofNat 0))))
        (funOf.isScottContinuous_left (funOf u (ofNat 1))))

end DomainTheory.DataTypesAsLattices
