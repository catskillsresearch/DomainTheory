module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eor
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2ehasZero
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2ehasPos

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.condSet {z x y : Pomega} (hz : IsRE z) (hx : IsRE x) (hy : IsRE y) :
    IsRE (condSet z x y) := by
  have hleft : REPred fun n => n ∈ x ∧ 0 ∈ z :=
    REPred.and hx.out (IsRE.hasZero hz)
  have hright : REPred fun n => n ∈ y ∧ ∃ k, k + 1 ∈ z :=
    REPred.and hy.out (IsRE.hasPos hz)
  constructor
  exact _root_.REPred.of_eq (REPred.or hleft hright) fun n => Iff.rfl

end DomainTheory.DataTypesAsLattices
