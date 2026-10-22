/-ai
The graph of a Scott continuous endomap of Pω is functional.

Functionality is the identity of the graph with the graph of its own application. Theorem 1.2 (i) gives that identity for a Scott continuous map.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem graph_mem_FUN {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    graph f ∈ FUN := by
  change graph f = graph (funOf (graph f))
  rw [theorem_1_2_i hf]

end DomainTheory.DataTypesAsLattices
