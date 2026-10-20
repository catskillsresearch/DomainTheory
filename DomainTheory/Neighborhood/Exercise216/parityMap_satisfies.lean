/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Example23
import DomainTheory.Neighborhood.Exercise216.Basic


namespace DomainTheory.Neighborhood.Exercise216

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB




/-- **`parityMap` satisfies its own defining equations.** Each is a direct instance of the
"shift formula" `Example23.parityMap_toElementMap_sigmaElt`, using that a leading `1` (resp. `01`,
`00`) fixes the scan of the concatenation `σ ++ τ` regardless of the tail `τ`
(`scan_append_true`/`scan_append_falseTrue`/`scan_append_falseFalse`). -/
theorem parityMap_satisfies : SatisfiesParityEquations Example23.parityMap where
  one x := by
    apply Element.ext
    intro Y
    rw [Example23.parityMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, _, hval⟩
      rwa [Example23.scan_append_true] at hval
    · intro hval
      exact ⟨[], by rw [cone_nil]; exact x.master_mem, by rwa [Example23.scan_append_true]⟩
  zeroOne x := by
    apply Element.ext
    intro Y
    rw [Example23.parityMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, _, hval⟩
      rwa [Example23.scan_append_falseTrue] at hval
    · intro hval
      exact ⟨[], by rw [cone_nil]; exact x.master_mem, by rwa [Example23.scan_append_falseTrue]⟩
  zeroZero x := by
    apply Element.ext
    intro Y
    rw [Example23.parityMap_toElementMap_sigmaElt, Example23.parityMap_toElementMap_mem]
    constructor
    · rintro ⟨τ, hτ, hval⟩
      exact ⟨τ, hτ, by rwa [Example23.scan_append_falseFalse] at hval⟩
    · rintro ⟨τ, hτ, hval⟩
      exact ⟨τ, hτ, by rwa [Example23.scan_append_falseFalse]⟩

end DomainTheory.Neighborhood.Exercise216
