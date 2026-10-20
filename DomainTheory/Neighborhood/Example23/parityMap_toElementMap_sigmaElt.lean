/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Approximable
import DomainTheory.Neighborhood.Example12
import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Example23.Basic


namespace DomainTheory.Neighborhood.Example23

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB












/-- **The "shift formula" for `parityMap`.** Reading off the parity of `σx` depends on `x` only
through *some* cone `cone τ ∈ x`, via the scan of the concatenation `σ ++ τ`: any deeper cone in
`sigmaElt`'s built-in up-closure is subsumed by monotonicity (`valElt_scan_mono`), so the longest
one — `σ ++ τ` itself — already witnesses the answer. This is the key computation behind Exercise
2.16's second half: `parityMap` genuinely satisfies its own defining equations. -/
theorem parityMap_toElementMap_sigmaElt (σ : Str) (x : B.Element) (Y : Set Example12.Token) :
    (parityMap.toElementMap (sigmaElt σ x)).mem Y ↔
      ∃ τ, x.mem (cone τ) ∧ (valElt (scan (σ ++ τ))).mem Y := by
  constructor
  · rintro ⟨Z, ⟨_, X, hX, hsub⟩, ρ, rfl, hval⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    rw [prepend_cone] at hsub
    exact ⟨τ, hX, valElt_scan_mono (cone_subset_cone.mp hsub) Y hval⟩
  · rintro ⟨τ, hτ, hval⟩
    exact ⟨cone (σ ++ τ), ⟨memB_cone _, cone τ, hτ, (prepend_cone σ τ).le⟩, σ ++ τ, rfl, hval⟩

end DomainTheory.Neighborhood.Example23
