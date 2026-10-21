/-ai
The combinator R lies in the set FUN of functional elements.

It is obtained by the lemma that the graph of a Scott-continuous map lies in FUN, applied to right continuity of sequencing at the numeral 0.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2_right_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Enumeration.graph_mem_FUN

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem Rcomb_mem_FUN : Rcomb ∈ FUN :=
  graph_mem_FUN (seq2_right_isScottContinuous (ofNat 0))

end DomainTheory.DataTypesAsLattices
