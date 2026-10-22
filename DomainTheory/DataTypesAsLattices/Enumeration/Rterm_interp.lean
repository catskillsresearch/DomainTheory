module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.seq2Term_interp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem Rterm_interp : interp Rterm (fun _ => botElem) = Rcomb := by
  unfold Rterm Rcomb
  apply congrArg graph
  funext x
  change interp (seq2Term .zero (.var 0)) (envSet (fun _ => botElem) 0 x) =
    seq2 (ofNat 0) x
  rw [seq2Term_interp]
  · simp [interp, envSet, Function.update]
  · trivial
  · exact Nat.zero_ne_add_one 7

end DomainTheory.DataTypesAsLattices
