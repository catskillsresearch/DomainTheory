/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality
import DomainTheory.DataTypesAsLattices.Enumeration.Basic


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




































































open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code











theorem REPred.exists_param {α} [Primcodable α] [Inhabited α] {p : α → ℕ → Prop}
    (hp : REPred fun q : α × ℕ => p q.1 q.2) :
    REPred fun a => ∃ n, p a n := by
  have hN : REPred fun q : ℕ × ℕ => p ((decode q.1).getD default) q.2 :=
    hp.comp (Computable.pair
      (Computable.option_getD (Computable.decode.comp Computable.fst)
        (Computable.const default))
      Computable.snd)
  have hex : REPred fun n : ℕ => ∃ m, p ((decode n).getD default) m :=
    REPred.exists (p := fun n m => p ((decode n).getD default) m) hN
  exact _root_.REPred.of_eq (hex.comp Computable.encode) fun a => by
    simp [encodek]

end DomainTheory.DataTypesAsLattices
