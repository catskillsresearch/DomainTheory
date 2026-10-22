/-ai
Interpreting the term for L in the constantly bottom environment yields the combinator L.

Unfold the term and the combinator, then simplify the interpretation, the updated environment, and the successor of the zero numeral.
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


theorem Lterm_interp : interp Lterm (fun _ => botElem) = Lcomb := by
  unfold Lterm Lcomb
  simp [interp, envSet, Function.update, succSet_ofNat]

end DomainTheory.DataTypesAsLattices
