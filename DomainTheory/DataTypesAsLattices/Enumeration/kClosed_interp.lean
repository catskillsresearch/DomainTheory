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


theorem kClosed_interp (ρ : ℕ → Pomega) : interp kClosed ρ = Kcomb := by
  unfold kClosed Kcomb
  simp [interp, envSet, Function.update]

end DomainTheory.DataTypesAsLattices
