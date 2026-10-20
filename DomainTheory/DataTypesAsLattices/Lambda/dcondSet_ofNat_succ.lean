/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_of_pos_not_zero


namespace DomainTheory.DataTypesAsLattices









theorem dcondSet_ofNat_succ (n : ℕ) (x y : Pomega) :
    dcondSet (ofNat (n + 1)) x y = y :=
  dcondSet_of_pos_not_zero (by simp [ofNat]) ⟨n, by simp [ofNat]⟩

end DomainTheory.DataTypesAsLattices
