module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4
public import DomainTheory.DataTypesAsLattices.Lambda.ofComb_combinatory
public import DomainTheory.DataTypesAsLattices.Lambda.theorem_2_4_more
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
  exact ofComb.combinatory _ _ filterEnv_combinatory

end DomainTheory.DataTypesAsLattices
