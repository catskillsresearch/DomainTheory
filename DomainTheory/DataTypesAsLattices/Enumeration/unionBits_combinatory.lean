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
import DomainTheory.DataTypesAsLattices.Enumeration.union_combinatory


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

























































theorem unionBits_combinatory : ∀ ks, IsCombinatory (unionBits ks)
  | [] => bot_combinatory
  | k :: ks => union_combinatory (ofNat_combinatory k) (unionBits_combinatory ks)

end DomainTheory.DataTypesAsLattices
