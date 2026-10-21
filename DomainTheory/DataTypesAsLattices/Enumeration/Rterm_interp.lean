/-ai
Interpreting Rterm in the constantly bottom environment yields the combinator R.

Unfold both sides and compare graphs at an arbitrary element x. The left side is the interpretation of sequencing the zero term with variable 0 in the environment updated at index 0 by x. The sequencing interpretation lemma applies: one avoidance side condition is immediate, and the other holds because 0 differs from 7. Simplifying interpretation and the environment update then gives sequencing of the numeral 0 with x.
ai-/
module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
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
