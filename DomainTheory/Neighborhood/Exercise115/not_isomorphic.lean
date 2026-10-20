/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise115.Basic
import DomainTheory.Neighborhood.Exercise115.flat_no_three_chain
import DomainTheory.Neighborhood.Exercise115.stem_three_chain


namespace DomainTheory.Neighborhood.Exercise115

open DomainTheory.Neighborhood NeighborhoodSystem














/-- **Exercise 1.15.** `flat` and `stem` are *not* isomorphic: an order-isomorphism would transport
`stem`'s strict 3-chain `⊥ ⊏ ↑{0,1} ⊏ ↑{0}` back to a strict 3-chain in `flat`, which has none. -/
theorem not_isomorphic : ¬ (flat ≅ᴰ stem) := by
  rintro ⟨e⟩
  obtain ⟨a, b, c, hab, hbc⟩ := stem_three_chain
  exact flat_no_three_chain
    ⟨e.symm a, e.symm b, e.symm c, e.symm.lt_iff_lt.mpr hab, e.symm.lt_iff_lt.mpr hbc⟩

end DomainTheory.Neighborhood.Exercise115
