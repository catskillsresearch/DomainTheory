module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pair
public import DomainTheory.DataTypesAsLattices.Retracts.comp

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem primrecPred_eq_scott_pair :
    PrimrecPred fun t : ℕ × ℕ × ℕ => t.1 = pair t.2.1 t.2.2 :=
  Primrec.eq.comp Primrec.fst
    (primrec_pair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

end DomainTheory.DataTypesAsLattices
