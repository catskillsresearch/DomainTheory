module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85
public import DomainTheory.DataTypesAsLattices.Enumeration.filterEnv_combinatory
public import DomainTheory.DataTypesAsLattices.Enumeration.filterC

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

theorem filterC_combinatory : IsCombinatory filterC := by
  rw [filterC, theorem_2_4.complete]
  exact ofComb_combinatory _ _ filterEnv_combinatory

end DomainTheory.DataTypesAsLattices
