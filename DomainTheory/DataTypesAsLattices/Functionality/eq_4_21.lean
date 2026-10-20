/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, (4.21).** `snd ∘ (f ⊗ f') = f' ∘ snd`. -/
theorem eq_4_21 (f f' : Pomega) :
    comp sndC (tensorR f f') = comp f' sndC := by
  simp only [comp]
  apply graph_ext
  intro u
  rw [sndC_app, tensorR_app, pairSeq_app_one, sndC_app]

end DomainTheory.DataTypesAsLattices
