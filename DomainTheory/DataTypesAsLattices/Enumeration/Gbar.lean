module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_15
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.FUN
public import DomainTheory.DataTypesAsLattices.Enumeration.barStepBody
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb
public import DomainTheory.DataTypesAsLattices.Enumeration.Gcomb_more

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

def Gbar : Pomega := funOf barComb Gcomb

namespace Gbar

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem combinatory : IsCombinatory Gbar :=
  .app barComb.combinatory Gcomb.combinatory

theorem mem_FUN : Gbar ∈ FUN := by
  change Gbar = graph (funOf Gbar)
  have h : Gbar = graph (fun x => barStepBody barComb Gcomb x) :=
    _root_.DomainTheory.DataTypesAsLattices.eq_3_15 Gcomb
  have hf : IsScottContinuous (fun x => barStepBody barComb Gcomb x) :=
    barStepBody.isScottContinuous_x barComb Gcomb
  rw [h, theorem_1_2.i hf]

end Gbar

end DomainTheory.DataTypesAsLattices
