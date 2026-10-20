/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.RE
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Computability.Basic
import DomainTheory.DataTypesAsLattices.Computability.IsREu2ebot
import DomainTheory.DataTypesAsLattices.Computability.IsREu2enumeral
import DomainTheory.DataTypesAsLattices.Computability.IsREu2eunion


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices




theorem IsRE.ofFinset (s : Finset ℕ) : IsRE (s : Set ℕ) := by
  induction s using Finset.induction with
  | empty =>
    simpa [botElem] using IsRE.bot
  | insert k s _hk ih =>
    have h : (insert k s : Set ℕ) = ofNat k ∪ (s : Set ℕ) := by
      ext; simp [ofNat]
    simpa [h] using IsRE.union (IsRE.numeral k) ih

end DomainTheory.DataTypesAsLattices
