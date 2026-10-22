/-ai
G-bar is combinatory.

It is the application of the bar combinator to G, and application preserves combinatory elements.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.barComb_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem Gbar_combinatory : IsCombinatory Gbar :=
  .app barComb_combinatory Gcomb_combinatory

end DomainTheory.DataTypesAsLattices
