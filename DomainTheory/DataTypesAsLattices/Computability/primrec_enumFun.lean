module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.enumFun
public import DomainTheory.DataTypesAsLattices.Retracts.comp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code




theorem primrec_enumFun (c : Code) : Nat.Primrec (enumFun c) := by
  have heval : Primrec fun t : ℕ => evaln t.unpair.2 c t.unpair.1 :=
    primrec_evaln.comp <|
      Primrec.pair
        (Primrec.pair (Primrec.snd.comp Primrec.unpair) (Primrec.const c))
        (Primrec.fst.comp Primrec.unpair)
  have h : Primrec fun t : ℕ =>
      bif (evaln t.unpair.2 c t.unpair.1).isSome
        then t.unpair.1 + 1 else 0 :=
    (Primrec.cond (Primrec.option_isSome.comp heval)
      (Primrec.succ.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.const 0)).of_eq fun t => by simp [Nat.succ_eq_add_one]
  exact Primrec.nat_iff.mp (h.of_eq fun _ => rfl)

end DomainTheory.DataTypesAsLattices
