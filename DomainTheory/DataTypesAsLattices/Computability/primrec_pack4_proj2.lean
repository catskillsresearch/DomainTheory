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



theorem primrec_pack4_proj2 : Primrec pack4_proj2 :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

end DomainTheory.DataTypesAsLattices
