module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.graph_mem_FUN

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem enumComp_mem_FUN (u v : Pomega) : enumComp u v ∈ FUN :=
  graph_mem_FUN (theorem_1_3 (funOf_isScottContinuous u) (funOf_isScottContinuous v))

end DomainTheory.DataTypesAsLattices
