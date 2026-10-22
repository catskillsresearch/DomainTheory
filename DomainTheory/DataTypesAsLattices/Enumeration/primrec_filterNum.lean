/-ai
The function filterNum is primitive recursive.

The conditional that tests beforeHalt on the two components of the unpairing, returns one more than the second component when the test holds, and returns 0 otherwise, is primitive recursive and agrees with filterNum. The equivalence between the two formulations of primitive recursiveness on the natural numbers transports the result.
ai-/
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
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
