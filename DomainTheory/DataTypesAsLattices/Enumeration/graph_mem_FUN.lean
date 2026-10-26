module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.FUN
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.theorem_1_2
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import Mathlib.Order.CompleteLattice.Defs
@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem graph_mem_FUN {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    graph f ∈ FUN := by
  change graph f = graph (funOf (graph f))
  rw [theorem_1_2.i hf]

end DomainTheory.DataTypesAsLattices
