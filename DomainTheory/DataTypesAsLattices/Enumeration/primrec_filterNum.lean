module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Functionality.pairElem
public import DomainTheory.DataTypesAsLattices.Retracts.comp
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.beforeHalt
public import DomainTheory.DataTypesAsLattices.Enumeration.BasicInst85
public import DomainTheory.DataTypesAsLattices.Enumeration.primrecPred_beforeHalt
public import DomainTheory.DataTypesAsLattices.Enumeration.filterNum

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

theorem primrec_filterNum : Nat.Primrec filterNum := by
  have h : Primrec filterNum :=
    (Primrec.ite (c := fun q : ℕ => beforeHalt q.unpair.1 q.unpair.2)
      (primrecPred_beforeHalt.comp
        (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
      (Primrec.succ.comp (Primrec.snd.comp Primrec.unpair))
      (Primrec.const 0)).of_eq fun q => by
      simp [filterNum]
  exact Primrec.nat_iff.mp h

end DomainTheory.DataTypesAsLattices
