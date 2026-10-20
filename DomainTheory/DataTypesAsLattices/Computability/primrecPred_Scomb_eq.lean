/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.RE
import all Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pair
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj1
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj2
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj3
public import DomainTheory.DataTypesAsLattices.Computability.primrec_pack4_proj4

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4

theorem primrecPred_Scomb_eq :
    PrimrecPred fun q : ℕ × ℕ =>
      q.1 = pair (pack4_proj1 q.2)
        (pair (pack4_proj2 q.2)
          (pair (pack4_proj3 q.2) (pack4_proj4 q.2))) :=
  Primrec.eq.comp Primrec.fst
    (primrec_pair.comp (primrec_pack4_proj1.comp Primrec.snd)
      (primrec_pair.comp (primrec_pack4_proj2.comp Primrec.snd)
        (primrec_pair.comp (primrec_pack4_proj3.comp Primrec.snd)
          (primrec_pack4_proj4.comp Primrec.snd))))

end DomainTheory.DataTypesAsLattices
