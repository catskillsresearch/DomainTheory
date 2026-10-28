module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4
public import DomainTheory.DataTypesAsLattices.Retracts.funRetract
public import DomainTheory.DataTypesAsLattices.Enumeration.funRetractTerm
public import DomainTheory.DataTypesAsLattices.Lambda.interp
@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem funRetract_combinatory : IsCombinatory funRetract := by
  rw [← funRetractTerm.interp]
  exact theorem_2_4.closed funRetractTerm

end DomainTheory.DataTypesAsLattices
