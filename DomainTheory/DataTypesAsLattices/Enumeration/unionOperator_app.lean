
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Enumeration.enumerationUnion_left_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Enumeration.enumerationUnion_right_isScottContinuous

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem unionOperator_app (x y : Pomega) :
    funOf (funOf (graph (fun x => graph (fun y => x ∪ y))) x) y = x ∪ y := by
  have hx : IsScottContinuous (fun x => graph (fun y => x ∪ y)) :=
    graph_const_isScottContinuous (fun x y => x ∪ y)
      (fun y => enumerationUnion_left_isScottContinuous y)
  have h1 : funOf (graph (fun x => graph (fun y => x ∪ y))) x =
      graph (fun y => x ∪ y) :=
    beta hx x
  rw [h1]
  exact beta (enumerationUnion_right_isScottContinuous x) y

end DomainTheory.DataTypesAsLattices
