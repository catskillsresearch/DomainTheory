module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Pomega.pair
public import DomainTheory.DataTypesAsLattices.Computability.pack4
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pair
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj1
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj2
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj3
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj4
public import DomainTheory.DataTypesAsLattices.Retracts.comp

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

theorem primrecPred_Scomb_eq :
    PrimrecPred fun q : ℕ × ℕ =>
      q.1 = pair (pack4.proj1 q.2)
        (pair (pack4.proj2 q.2)
          (pair (pack4.proj3 q.2) (pack4.proj4 q.2))) :=
  Primrec.eq.comp Primrec.fst
    (primrec_pair.comp (primrec_pack4_proj1.comp Primrec.snd)
      (primrec_pair.comp (primrec_pack4_proj2.comp Primrec.snd)
        (primrec_pair.comp (primrec_pack4_proj3.comp Primrec.snd)
          (primrec_pack4_proj4.comp Primrec.snd))))

end DomainTheory.DataTypesAsLattices
