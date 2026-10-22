/-ai
The combinator R is combinatory.

Rewrite by the interpretation of the closed term Rterm, and apply theorem 2.4, which says that the interpretation of any closed term in the constantly bottom environment is combinatory.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.Rterm_interp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem Rcomb_combinatory : IsCombinatory Rcomb := by
  rw [← Rterm_interp]
  exact theorem_2_4_closed Rterm

end DomainTheory.DataTypesAsLattices
