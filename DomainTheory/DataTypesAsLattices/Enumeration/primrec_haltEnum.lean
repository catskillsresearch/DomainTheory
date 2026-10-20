module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedFromG
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSemigroup
public import DomainTheory.DataTypesAsLattices.Enumeration.haltEnum

@[expose] public section

set_option linter.unusedSectionVars false

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable

open Nat.Partrec (Code)

open Nat.Partrec.Code

theorem primrec_haltEnum : Primrec haltEnum := by
  have heval : Primrec fun t : ℕ =>
      evaln t.unpair.2 (Denumerable.ofNat Code t.unpair.1) 0 :=
    primrec_evaln.comp <|
      Primrec.pair
        (Primrec.pair (Primrec.snd.comp Primrec.unpair)
          ((Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.const 0)
  exact (Primrec.cond (Primrec.option_isSome.comp heval)
    (Primrec.succ.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.const 0)).of_eq fun t => by
    simp [haltEnum]

end DomainTheory.DataTypesAsLattices
