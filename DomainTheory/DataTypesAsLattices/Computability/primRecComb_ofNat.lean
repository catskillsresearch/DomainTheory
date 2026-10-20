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

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code



attribute [local irreducible] pack4_proj1 pack4_proj2 pack4_proj3 pack4_proj4







theorem primRecComb_ofNat (a f : Pomega) (n : ℕ) :
    funOf (primRecComb a f) (ofNat n) = primRecVal a f n := by
  have hgraph := primRecStep_graph_of a f
  have hfix := theorem_2_5 (primRecStep_isScottContinuous a f)
  simp only [primRecComb]
  rw [← hgraph, hfix, ← eq_2_27, primRecHat_ofNat]

end DomainTheory.DataTypesAsLattices
