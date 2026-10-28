module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Computability.composeC
public import DomainTheory.DataTypesAsLattices.Lambda.FUN
public import DomainTheory.DataTypesAsLattices.Retracts.funRetract
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Computability.SK_comp
public import DomainTheory.DataTypesAsLattices.Enumeration.funRetract_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.graph_mem_FUN

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

def enumComp (u v : Pomega) : Pomega :=
  graph (fun x => funOf u (funOf v x))

namespace enumComp
open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem app (u v x : Pomega) :
    funOf (enumComp u v) x = funOf u (funOf v x) :=
  beta (theorem_1_3 (funOf.isScottContinuous u) (funOf.isScottContinuous v)) x

theorem eq_compose (u v : Pomega) :
    enumComp u v = funOf funRetract (composeC u v) := by
  rw [funRetract.app, composeC]
  apply congrArg graph
  funext x
  exact (SK_comp u v x).symm

theorem combinatory {u v : Pomega}
    (hu : IsCombinatory u) (hv : IsCombinatory v) :
    IsCombinatory (enumComp u v) := by
  rw [enumComp.eq_compose]
  exact .app funRetract_combinatory (composeC.combinatory hu hv)

theorem mem_FUN (u v : Pomega) : enumComp u v ∈ FUN :=
  graph_mem_FUN (theorem_1_3 (funOf.isScottContinuous u) (funOf.isScottContinuous v))

end enumComp

end DomainTheory.DataTypesAsLattices
