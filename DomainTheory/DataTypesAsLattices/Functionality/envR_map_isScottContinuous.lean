module

public import DomainTheory.DataTypesAsLattices.Retracts.lambR
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem envR_map_isScottContinuous :
    IsScottContinuous (fun t => graph (fun n => funOf lambR (funOf t n))) :=
  graph_const_isScottContinuous
    (fun t n => funOf lambR (funOf t n))
    (fun n => theorem_1_3 (funOf.isScottContinuous lambR)
      (funOf.isScottContinuous_left n))

end DomainTheory.DataTypesAsLattices
