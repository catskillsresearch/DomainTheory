/-ai
For each partial-recursive code c, the stage-bounded enumerator enumFun c is primitive recursive.

The bounded evaluation of the second unpaired component at c on the first unpaired component is primitive recursive by composing primrec_evaln. The function which returns one more than the first unpaired component when that evaluation is defined, and returns 0 otherwise, is primitive recursive by a conditional, rewritten by the successor equation. The characterization Nat.Primrec follows by nat_iff and a reflexive rewriting.
ai-/
module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4


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
