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
public import DomainTheory.DataTypesAsLattices.Computability.pairComb_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.botElem_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.unpairFstC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.unpairSndC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.primRecOpC_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4





































theorem precEnv_combinatory {f g : Pomega}
    (hf : IsCombinatory f) (hg : IsCombinatory g) :
    ∀ i, IsCombinatory (precEnv f g i)
  | 3 => primRecOpC_combinatory
  | 4 => hf
  | 5 => hg
  | 6 => unpairFstC_combinatory
  | 7 => unpairSndC_combinatory
  | 8 => pairComb_combinatory
  | 0 | 1 | 2 => botElem_combinatory
  | _ + 9 => botElem_combinatory

end DomainTheory.DataTypesAsLattices
