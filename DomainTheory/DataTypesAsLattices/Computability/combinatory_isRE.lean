/-ai
Every combinatory element of Pω is recursively enumerable. This is one direction of the appendix equivalence.

Induct on the combinatory derivation. Zero, successor, predecessor, conditional, K, and S are recursively enumerable by the corresponding theorems, and application preserves recursive enumerability.
ai-/
module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2ezeroC
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2efunOf
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2esucC
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2epredC
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2eKcomb
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2econdC
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2eScomb

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

/-- Combinatory elements are r.e. (one direction of the appendix equivalence). -/
theorem combinatory_isRE {u : Pomega} (hu : IsCombinatory u) : IsRE u := by
  induction hu with
  | zero => exact IsRE.zeroC
  | suc => exact IsRE.sucC
  | pred => exact IsRE.predC
  | cond => exact IsRE.condC
  | K => exact IsRE.Kcomb
  | S => exact IsRE.Scomb
  | app _ _ iu iv => exact IsRE.funOf iu iv

end DomainTheory.DataTypesAsLattices
