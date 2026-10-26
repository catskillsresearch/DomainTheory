module

public import DomainTheory.DataTypesAsLattices.Enumeration.barStepBody
public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStepBody

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

def barStep (B : Pomega) : Pomega :=
  graph (fun u => graph (fun x => barStepBody B u x))

namespace barStep

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem app (B u : Pomega) :
    funOf (barStep B) u = graph (fun x => barStepBody B u x) :=
  beta (graph_const_isScottContinuous (fun u x => barStepBody B u x)
    (fun x => barStepBody.isScottContinuous_u B x)) u

theorem isScottContinuous : IsScottContinuous barStep :=
  graph_const_isScottContinuous
    (fun B u => graph (fun x => barStepBody B u x))
    (fun u => graph_const_isScottContinuous
      (fun B x => barStepBody B u x)
      (fun x => barStepBody.isScottContinuous_B u x))

end barStep

end DomainTheory.DataTypesAsLattices
