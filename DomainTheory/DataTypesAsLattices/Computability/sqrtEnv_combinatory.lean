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
public import DomainTheory.DataTypesAsLattices.Computability.mulC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.leC_combinatory
public import DomainTheory.DataTypesAsLattices.Computability.botElem_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4
























theorem sqrtEnv_combinatory : ∀ i, IsCombinatory (sqrtEnv i)
  | 3 => leC_combinatory
  | 4 => mulC_combinatory
  | 0 | 1 | 2 => botElem_combinatory
  | _ + 5 => botElem_combinatory

end DomainTheory.DataTypesAsLattices
