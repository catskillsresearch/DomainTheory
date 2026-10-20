/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand
import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
import DomainTheory.DataTypesAsLattices.Computability.IsREu2epair_mem
import DomainTheory.DataTypesAsLattices.Computability.IsREu2eeSubset


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- **Scott 1976, Appendix.** Application of r.e. elements is r.e. -/
theorem IsRE.funOf {u x : Pomega} (hu : IsRE u) (hx : IsRE x) : IsRE (u ⬝ x) := by
  have hand : REPred fun q : ℕ × ℕ => e q.1 ⊆ x ∧ pair q.1 q.2 ∈ u :=
    REPred.and ((IsRE.eSubset hx).comp Computable.fst) (IsRE.pair_mem hu)
  have hex : REPred fun m => ∃ n, e n ⊆ x ∧ pair n m ∈ u :=
    REPred.exists (p := fun m n => e n ⊆ x ∧ pair n m ∈ u)
      (hand.comp (Primrec.pair Primrec.snd Primrec.fst).to_comp)
  exact hex.of_eq fun _ => Iff.rfl

end DomainTheory.DataTypesAsLattices
