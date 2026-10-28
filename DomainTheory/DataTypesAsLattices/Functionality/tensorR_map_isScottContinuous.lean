
module

public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem tensorR_map_isScottContinuous (a b : Pomega) :
    IsScottContinuous (fun u =>
      pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1)))) :=
  continuous_tuple
    (fun y => pairSeq_isScottContinuous_left y)
    (fun x => pairSeq_isScottContinuous_right x)
    (theorem_1_3 (funOf.isScottContinuous a) (funOf.isScottContinuous_left (ofNat 0)))
    (theorem_1_3 (funOf.isScottContinuous b) (funOf.isScottContinuous_left (ofNat 1)))

end DomainTheory.DataTypesAsLattices
