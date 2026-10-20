/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.mem_funOf_ofNat

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code











theorem funOf_ofNat_mem_re {u : Pomega} (hu : IsRE u) :
    REPred fun q : ℕ × ℕ => q.2 ∈ funOf u (ofNat q.1) := by
  have h0 : REPred fun q : ℕ × ℕ => pair 0 q.2 ∈ u :=
    (IsRE.pair_mem hu).comp
      (Primrec.pair (Primrec.const 0) Primrec.snd).to_comp
  have hpow : REPred fun q : ℕ × ℕ => pair (2 ^ q.1) q.2 ∈ u :=
    (IsRE.pair_mem hu).comp
      (Primrec.pair (primrec_twoPow.comp Primrec.fst) Primrec.snd).to_comp
  exact _root_.REPred.of_eq (REPred.or h0 hpow) fun q =>
    (mem_funOf_ofNat u q.1 q.2).symm

end DomainTheory.DataTypesAsLattices
