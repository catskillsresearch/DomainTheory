module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability.primrec_realized
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Enumeration.primrec_filterNum
public import DomainTheory.DataTypesAsLattices.Computability.Realizes
public import DomainTheory.DataTypesAsLattices.Enumeration.filterNum

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

noncomputable def filterRealizer : Pomega :=
  (primrec_realized primrec_filterNum).choose

namespace filterRealizer

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

theorem combinatory : IsCombinatory filterRealizer :=
  (primrec_realized primrec_filterNum).choose_spec.1

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem realizes : Realizes filterRealizer filterNum :=
  (primrec_realized primrec_filterNum).choose_spec.2

end filterRealizer

end DomainTheory.DataTypesAsLattices
