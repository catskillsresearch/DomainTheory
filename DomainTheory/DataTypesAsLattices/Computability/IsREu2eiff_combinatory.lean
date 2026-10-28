module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Computability.IsRE
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.combinatory_isRE
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2ecombinatory

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem IsRE.iff_combinatory {u : Pomega} : IsRE u ↔ IsCombinatory u :=
  ⟨IsRE.combinatory, combinatory_isRE⟩

end DomainTheory.DataTypesAsLattices
