module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability.pairComb
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Enumeration.filterRealizer
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem filterSeq_isScottContinuous :
    IsScottContinuous fun v =>
      graph (fun j => funOf filterRealizer (funOf (funOf pairComb v) j)) :=
  graph_const_isScottContinuous
    (fun v j => funOf filterRealizer (funOf (funOf pairComb v) j))
    (fun j =>
      theorem_1_3 (f := fun w => funOf filterRealizer w)
        (g := fun v => funOf (funOf pairComb v) j)
        (funOf.isScottContinuous filterRealizer)
        (theorem_1_3 (f := fun w => funOf w j) (g := fun v => funOf pairComb v)
          (funOf.isScottContinuous_left j)
          (funOf.isScottContinuous pairComb)))

end DomainTheory.DataTypesAsLattices
